/* dk_ref.c: Dedukti files (the lambda-Pi calculus modulo rewriting) checked as firings of
 * tcalc_ref's step, on the binder layer of ../binders.
 *
 *   usage: dk_ref [--coc] [--eta] [--ll] [--type-lhs] [-q] [--stats] FILE.dk ...
 *   exit:  0 accepted, 1 refused, 2 no verdict (a feature not hosted, or a resource limit)
 *   Files given together share one signature (a module per file, named after it).
 *   Not hosted (no verdict): AC symbols (defac, defacu); some rule typings under constraints.
 *   --type-lhs refuses a rule whose typing constraints are refuted by facts, in every safe extension
 *   of the signature (never by the current signature alone, whose definable symbols may get rules):
 *   no solution (nosol: rigid heads that differ, a bound variable against a term that cannot mention
 *   it, Type against a term of type Type), or no well-founded solution (nowf: the occurs check
 *   through static symbols).  Without it such a rule is admitted, being sound, and reported (a NOTE
 *   line unless -q).
 *
 * Every judgment that affects the verdict is a fact made by an admitted firing; the C is the .dk
 * reader and the work order (which rule next, on which facts, and a memo of facts by term).
 * Terms are de Bruijn terms of the binder layer: app(f, a), lam(dom, body), pi(dom, cod), cst(K)
 * (K the code of a symbol), type, kind, none (a lambda without domain), var(n).
 *
 * Judgments, positive (true for good once made):
 *   ev(t, s, r)  mentions(t, k)                 the binder layer
 *   rd(a, b)            a reduces to b in zero or more steps of beta, delta and the file's rules,
 *                       at any position
 *   conv(a, b)          a and b are convertible, by Dedukti's algorithm (lambda domains ignored;
 *                       with --eta, eta-expansion against a non-abstraction)
 *   ctx(G) lookup(G, n, A) ty(G, t, A) tys(G, A, s)   typing of lambda-Pi (lambda-Pi-CoC: --coc)
 *   decl(K, A) static(K) defn(K, t) rules(K, L)       the signature; injective(K) records a symbol
 *                       declared `injective` (the user's claim, trusted as Dedukti trusts it)
 * Rule typing (Dedukti's subject-reduction check under constraints), hypothetically:
 *   hyp(X, Y, G)        a context with the hypothesis X == Y (it binds nothing)
 *   cv(G, X, Y)         X == Y in every instance satisfying G's hypotheses (conversion, the
 *                       hypotheses, symmetry, transitivity, weakening, congruence, reduction, and
 *                       injectivity of static and injective heads)
 *   sub(L, T)  oblig(G, L, X, A)   an argument conversion X == A at an application inside L (also
 *                       under its pattern abstractions, stated abstracted): every typable instance of
 *                       L satisfies it, so a hypothesis is admitted only with its oblig fact
 * A rule is admitted when its context (with hypotheses, each justified) is well formed, the
 * left-hand side has a type T and the right-hand side a type convertible to T under them.
 * Judgments, negative: valid while the rule set is unchanged, so they carry the epoch E, a name
 * minted by every rule admission, and every firing that uses one reads epoch(E):
 *   head(w, h, n) shape(w, s) lt(n, k)               (structural)
 *   hn(w, E)            w is in weak head normal form: no beta redex, no definition, and every rule
 *                       of its head symbol fails to match (nmall, nomatch)
 *   wh(a, w, E)  nf(a, n, E)  nfw(w, n, E)           weak head / strong normal forms
 *   nomatch(R, w, E)    rule R does not match w: a rigid position whose head clashes, a pattern
 *                       variable whose instance (in normal form) mentions a forbidden bound
 *                       variable, or two instances of a repeated pattern variable that are not
 *                       convertible
 *   nc(w1, w2, E)  notconv(a, b, E)                  not convertible
 * Negative judgments are evidence relative to confluence, as Dedukti's own algorithm is.
 *
 * Matching (the relation of Saillard's thesis and of Hondet and Blanqui, FSCD 2020, 2.1): a rule is
 * compiled, when admitted, into one match firing and its failure firings.  A rigid pattern position
 * reads rd(target, shape); a pattern variable X y1..ya under d pattern binders reads rd(target, t')
 * and ev(t', rho, body) with rho = bl_rho(d, y, a) (t' is the target, or its normal form when the
 * target itself mentions a forbidden variable, as Dedukti's force_solve); its solution is
 * lam^a(body); a repeated variable reads conv between its solutions; the right-hand side is
 * ev(rhs, sigma, r).  So an instance mentioning a variable bound outside the redex matches, and an
 * instance mentioning the pattern's own binder does not, at every depth and arity.  A bracket {t}
 * is matched as a variable of arity 0 and then reads conv(instance, t[sigma]); a guard that fails
 * refuses the file, as Dedukti's does.
 */
#include "../binders/bl.h"
#include "../specialize/tcs.h"

#include <ctype.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

/* ============================================================================================
 * Allocation, verdicts.
 * ========================================================================================== */

static void *xr(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("dk_ref: NO VERDICT: out of memory\n", stderr);
    exit(2);
  }
  return q;
}
#define GROW(arr, len, cap)                                 \
  do {                                                      \
    if ((len) >= (cap)) {                                   \
      (cap) = (cap) ? 2 * (cap) : 16;                       \
      (arr) = xr((arr), (size_t)(cap) * sizeof *(arr));     \
    }                                                       \
  } while (0)

static const char *cur_file = "?";
static uint32_t cur_line;
static bool QUIET, STATS, COC, ETA, LL, TYPE_LHS;
static uint32_t n_hyp_rules; /* rules admitted under typing hypotheses */
/* For harness checks only.  DK_FAULT plants a fault in a rule, with the work order exploiting it:
 *   1 the application rule does not read the argument's conversion
 *   3 a repeated pattern variable's instances are not compared
 *   4 products are convertible whatever their domains
 *   6 a refutation takes any constant head as rigid (the static fact is not read)
 * (BL_FAULT plants the binder layer's faults: 5 is the missing depth - arity transport.)
 * DK_LIE makes the work order propose a false fact; the step must refuse each:
 *   1 an application's argument is given the function's conversion fact
 *   2 a repeated pattern variable's comparison is given a reflexivity fact
 *   3 a pattern variable's solution is computed with the renaming that lacks the transport
 *   4 a rule's context gets the hypothesis "the right-hand side's type is the left-hand side's",
 *     and the admission is given the justification of the context without it
 *   5 a refutation "no well-founded solution" is given the reflexivity v == v in place of the
 *     equation v == t it rests on */
static int FAULT, LIE;
enum { BY_READER, BY_FIRING, BY_FACT, BY_ORDER };
static const char *by_name[] = {"by the reader", "by a refused firing", "by a fact made by firings",
                                "by the work order: no derivation found"};

static _Noreturn void refuse(int by, const char *fmt, ...) {
  va_list ap;
  fprintf(stderr, "REFUSED (%s) %s:%u: ", by_name[by], cur_file, cur_line);
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}
static _Noreturn void noverdict(const char *fmt, ...) {
  va_list ap;
  fprintf(stderr, "NO VERDICT %s:%u: ", cur_file, cur_line);
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(2);
}

/* Deep recursion runs on a large stack; past its room the answer is no verdict. */
#define STACK_SIZE ((size_t)1 << 30)
static char *stack_base;
static size_t stack_room;
static void deep(void) {
  char here;
  size_t used = stack_base > &here ? (size_t)(stack_base - &here) : (size_t)(&here - stack_base);
  if (stack_base && used > stack_room) noverdict("nesting too deep for this checker's stack");
}

/* ============================================================================================
 * The step, the binder layer, symbols and terms.
 * ========================================================================================== */

static tr_ctx *C;
static tr_state *S;
static rk_engine E;
static bl *B;

static uint32_t c_app, c_lam, c_pi, c_cst, c_type, c_kind, c_none;
static uint32_t f_rd, f_conv, f_ctx, f_nil, f_cons, f_lookup, f_ty, f_tys, f_decl, f_static, f_defn, f_rules, f_rl;
static uint32_t f_epoch, f_head, f_hn, f_wh, f_nomatch, f_nmall, f_lt, f_nf, f_nfw, f_nc, f_notconv, f_shape;
static uint32_t f_sv, f_sc, f_sl, f_sp, f_st, f_sk, f_sn, f_z, f_s, f_var, f_pv;
/* Rule typing under hypotheses (Dedukti's subject-reduction check under constraints):
 *   hyp(X, Y, G)        a context G with the hypothesis X == Y (it binds no variable)
 *   cv(G, X, Y)         X and Y are convertible in every instance satisfying G's hypotheses
 *   sub(L, T)           T is L or an application subterm of L (outside binders)
 *   oblig(G, L, X, A)   at an application F U inside L, U has type X and F's type is a product
 *                       with domain A: every typable instance of L makes X == A, so the hypothesis
 *                       is necessary, not assumed */
static uint32_t f_hyp, f_cv, f_sub, f_oblig, f_brk, f_just, f_shk, f_pin;
/* Refuted typing constraints (what --type-lhs refuses; otherwise reported, the rule being sound):
 *   rocc(V, T)          the variable V occurs in T, T not V itself, along applications headed by
 *                       static symbols and abstractions: every reduct of an instance of T keeps,
 *                       strictly inside it, a reduct of V's instance
 *   rshape(T, S)        T's top is rigid in every instance and every safe extension: a static
 *                       spine sc(K, N), a product sp, Type st or Kind sk
 *   nosol(G, X, Y)      cv(G, X, Y) with rigid tops that differ: G's hypotheses have no solution
 *   nowf(G, V, T)       cv(G, V, T) and rocc(V, T): every solution gives V an instance without a
 *                       normal form (no well-founded solution; a fixpoint of a non-terminating rule
 *                       can still be one, so the left-hand side may have typable instances) */
static uint32_t f_rocc, f_rshape, f_nosol, f_nowf;
/* Obligations under nested pattern abstractions, and refutations under their binders:
 *   obchk(G, U, A, X, Y)  every instance satisfying G's hypotheses in which U's instance is typable
 *                       at a type convertible to A's instance satisfies X == Y (at a constant-headed
 *                       U of type T: T == A; through an abstraction checked against a product, the
 *                       body's equation, stated abstracted)
 *   nosol(G, X, Y) is also made from cv(cons(D, G), U, V) where the binder var(0) is U, or occurs in
 *   U along static heads, and V is a shift (cannot mention it): with var(0) kept as a variable, which
 *   no instance of G's variables mentions, no reduct of V's instance ever contains it; and a nosol of
 *   cons(D, G) is one of G (a solution of G, with var(0) kept, would be one of cons(D, G)). */
static uint32_t f_obchk;
/* injective(K): K was declared `injective`, a claim Dedukti trusts and so does this checker */
static uint32_t f_inj;
static bool decl_injective;
static tr_term TYPE, KIND, NONE, NIL, ZERO, ID, SH, SL;

static tr_term T0(uint32_t f) { return tr_app(C, f, NULL); }
static tr_term T1(uint32_t f, tr_term a) { return tr_app(C, f, &a); }
static tr_term T2(uint32_t f, tr_term a, tr_term b) {
  tr_term x[2] = {a, b};
  return tr_app(C, f, x);
}
static tr_term T3(uint32_t f, tr_term a, tr_term b, tr_term c) {
  tr_term x[3] = {a, b, c};
  return tr_app(C, f, x);
}
static tr_term T4(uint32_t f, tr_term a, tr_term b, tr_term c, tr_term d) {
  tr_term x[4] = {a, b, c, d};
  return tr_app(C, f, x);
}
static tr_term T5(uint32_t f, tr_term a, tr_term b, tr_term c, tr_term d, tr_term e) {
  tr_term v[5] = {a, b, c, d, e};
  return tr_app(C, f, v);
}
static tr_term L(uint32_t i) { return tr_local(C, i); }
static tr_term APP(tr_term f, tr_term a) { return T2(c_app, f, a); }
static tr_term LAM(tr_term d, tr_term b) { return T2(c_lam, d, b); }
static tr_term PI(tr_term a, tr_term b) { return T2(c_pi, a, b); }
static tr_term CST(uint32_t k) { return T1(c_cst, tr_code(C, k)); }
static tr_term NAT(uint32_t n) { return bl_nat(B, n); }
static tr_term VAR(uint32_t n) { return bl_var(B, n); }
static tr_term VART(tr_term n) { return T1(f_var, n); }

static uint32_t head_sym(tr_term t) { return tr_term_kind(C, t) == TR_APP ? tr_term_symbol(C, t) : UINT32_MAX; }
static tr_term arg(tr_term t, uint32_t i) { return tr_term_arg(C, t, i); }
static bool is_app(tr_term t) { return head_sym(t) == c_app; }
static bool is_lam(tr_term t) { return head_sym(t) == c_lam; }
static bool is_pi(tr_term t) { return head_sym(t) == c_pi; }
static bool is_cst(tr_term t, uint32_t *k) {
  if (head_sym(t) != c_cst) return false;
  if (k) *k = (uint32_t)tr_term_code(C, arg(t, 0));
  return true;
}
static bool is_var(tr_term t, uint32_t *n) { return bl_var_index(B, t, n); }
/* The head of an application spine and its number of arguments. */
static tr_term spine(tr_term t, uint32_t *n) {
  uint32_t k = 0;
  while (is_app(t)) t = arg(t, 0), k++;
  *n = k;
  return t;
}
/* Argument i (0-based, from the left) of a spine with n arguments. */
static tr_term spine_arg(tr_term t, uint32_t n, uint32_t i) {
  for (uint32_t k = n; k-- > i + 1;) t = arg(t, 0);
  return arg(t, 1);
}
static tr_term strip(tr_term t, uint32_t k) { /* drop the last k arguments */
  while (k--) t = arg(t, 0);
  return t;
}

/* ---- facts ---- */
static tr_term RD(tr_term a, tr_term b) { return T2(f_rd, a, b); }
static tr_term CONV(tr_term a, tr_term b) { return T2(f_conv, a, b); }
static tr_term TY(tr_term g, tr_term t, tr_term a) { return T3(f_ty, g, t, a); }
static tr_term TYS(tr_term g, tr_term a, tr_term s) { return T3(f_tys, g, a, s); }
static tr_term EV(tr_term t, tr_term s, tr_term r) { return bl_ev_fact(B, t, s, r); }
static tr_term CONS(tr_term a, tr_term g) { return T2(f_cons, a, g); }
static tr_term WH(tr_term a, tr_term w, tr_term e) { return T3(f_wh, a, w, e); }

/* ============================================================================================
 * Memo tables: 64-bit key -> occurrence, value, stamp.
 * ========================================================================================== */

typedef struct {
  uint64_t key;
  tr_occ occ;
  tr_term val;
  uint32_t stamp;
} ment;
typedef struct {
  ment *v;
  size_t cap, n;
} map;
static uint64_t mh(uint64_t k) {
  k ^= k >> 33, k *= 0xff51afd7ed558ccdULL, k ^= k >> 33;
  return k;
}
static ment *map_find(map *m, uint64_t key) {
  if (!m->cap) return NULL;
  for (size_t j = mh(key) & (m->cap - 1);; j = (j + 1) & (m->cap - 1)) {
    if (!m->v[j].key) return NULL;
    if (m->v[j].key == key) return &m->v[j];
  }
}
static ment *map_put(map *m, uint64_t key) {
  if (2 * (m->n + 1) > m->cap) {
    size_t cap = m->cap ? 2 * m->cap : 1024;
    ment *nv = xr(NULL, cap * sizeof *nv);
    memset(nv, 0, cap * sizeof *nv);
    for (size_t i = 0; i < m->cap; i++)
      if (m->v[i].key) {
        size_t j = mh(m->v[i].key) & (cap - 1);
        while (nv[j].key) j = (j + 1) & (cap - 1);
        nv[j] = m->v[i];
      }
    free(m->v);
    m->v = nv;
    m->cap = cap;
  }
  size_t j = mh(key) & (m->cap - 1);
  while (m->v[j].key && m->v[j].key != key) j = (j + 1) & (m->cap - 1);
  if (!m->v[j].key) m->n++;
  m->v[j].key = key;
  return &m->v[j];
}
static uint64_t K2(tr_term a, tr_term b) { return ((uint64_t)a << 32 | b) + 1; }

/* ============================================================================================
 * Symbols of the signature.
 * ========================================================================================== */

enum { SK_STATIC, SK_DEFINABLE, SK_DEFN, SK_THM };
typedef struct {
  char *name; /* module.id */
  int kind;
  tr_occ decl, stat, defn, rules; /* the facts: decl(K, A), static(K), defn(K, t), rules(K, L) */
  tr_occ inj;                     /* injective(K), for a symbol declared injective */
  tr_term type, body;
  uint32_t *rl; /* this symbol's rewrite rules, in the order admitted */
  size_t nrl, caprl;
} sym;
static sym *SY;
static uint32_t nsy, capsy;
static uint32_t *symtab;
static size_t capsymtab;

static uint64_t strhash(const char *s) {
  uint64_t h = 1469598103934665603ULL;
  for (; *s; s++) h = (h ^ (unsigned char)*s) * 1099511628211ULL;
  return h;
}
static uint32_t sym_find(const char *name) {
  if (!capsymtab) return UINT32_MAX;
  for (size_t j = strhash(name) & (capsymtab - 1);; j = (j + 1) & (capsymtab - 1)) {
    if (!symtab[j]) return UINT32_MAX;
    if (!strcmp(SY[symtab[j] - 1].name, name)) return symtab[j] - 1;
  }
}
static uint32_t sym_add(const char *name) {
  if (2 * (nsy + 1) > capsymtab) {
    size_t cap = capsymtab ? 2 * capsymtab : 1024;
    uint32_t *t = xr(NULL, cap * sizeof *t);
    memset(t, 0, cap * sizeof *t);
    for (uint32_t i = 0; i < nsy; i++) {
      size_t j = strhash(SY[i].name) & (cap - 1);
      while (t[j]) j = (j + 1) & (cap - 1);
      t[j] = i + 1;
    }
    free(symtab);
    symtab = t;
    capsymtab = cap;
  }
  GROW(SY, nsy, capsy);
  memset(&SY[nsy], 0, sizeof SY[nsy]);
  SY[nsy].name = strcpy(xr(NULL, strlen(name) + 1), name);
  size_t j = strhash(name) & (capsymtab - 1);
  while (symtab[j]) j = (j + 1) & (capsymtab - 1);
  symtab[j] = nsy + 1;
  return nsy++;
}

/* ============================================================================================
 * The fixed rules.
 * ========================================================================================== */

static rk_rule R_rd_refl, R_rd_trans, R_rd_beta, R_rd_delta, R_rd_app, R_rd_lam, R_rd_pi;
static rk_rule R_cv_refl, R_cv_redl, R_cv_redr, R_cv_app, R_cv_lam, R_cv_pi, R_cv_etal, R_cv_etar;
static rk_rule R_ctx_nil, R_ctx_cons[2], R_lookup0, R_lookupS, R_ty_type, R_ty_cst, R_ty_var, R_tys[2];
static rk_rule R_ty_pi[2][2], R_ty_lam[2], R_ty_lamn[2], R_ty_app;
static rk_rule R_just_nil, R_just_cons, R_just_hyp, R_pin, R_oblig_var;
static rk_rule R_rocc_here, R_rocc_arg, R_rocc_fun, R_rshape_cst, R_rshape_pi, R_rshape_sort[2], R_nosol, R_nowf;
static rk_rule R_obchk_cst, R_obchk_lam, R_oblig_chk, R_rocc_lam, R_rocc_lam_here, R_nosol_bindv, R_nosol_bindo,
    R_nosol_up, R_nosol_sort;
static rk_rule R_ctx_hyp, R_lookup_hyp, R_cv_conv, R_cv_hyp, R_cv_sym, R_cv_trans, R_cv_wk_hyp, R_cv_wk_cons,
    R_cvh_app, R_cvh_pi, R_cvh_lam, R_cv_red, R_cv_dec[2][2], R_sub_refl, R_sub_fun, R_sub_arg, R_oblig,
    R_oblig_lamty, R_oblig_lam;
static rk_rule R_epoch0, R_head_var, R_head_cst, R_head_app, R_hn_leaf[3], R_hn_pi, R_hn_lam, R_hn_var, R_hn_static,
    R_hn_def, R_nmall_nil, R_nmall_nm, R_nmall_short, R_nm_lift, R_lt0, R_ltS, R_wh, R_nf, R_nfw_var, R_nfw_cst,
    R_nfw_leaf[3], R_nfw_app, R_nfw_lam, R_nfw_pi, R_shape_leaf[3], R_shape_pi, R_shape_lam, R_shape_var, R_shape_cst,
    R_nc_shape, R_nc_appf, R_nc_appa, R_nc_lam, R_nc_pid, R_nc_pic, R_nc_etal, R_nc_etar, R_notconv;

static void bin_cong(rk_rule *r, const char *what, uint32_t fact, uint32_t con, bool read_first, bool read_second,
                     bool param_first, bool param_second) {
  /* fact(con(L0, L1), con(L2, L3)) from fact(L0, L2) and fact(L1, L3) */
  rk_init(r, what, 4);
  if (read_first) rk_read(r, T2(fact, L(0), L(2)));
  if (read_second) rk_read(r, T2(fact, L(1), L(3)));
  rk_make(r, T2(fact, T2(con, L(0), L(1)), T2(con, L(2), L(3))));
  if (param_first) rk_param(r, 0), rk_param(r, 2);
  if (param_second) rk_param(r, 1), rk_param(r, 3);
}

static void init_rules(void) {
  tr_term sorts[2] = {TYPE, KIND};
  /* reduction */
  rk_init(&R_rd_refl, "rd refl", 1);
  rk_make(&R_rd_refl, RD(L(0), L(0)));
  rk_param(&R_rd_refl, 0);
  rk_init(&R_rd_trans, "rd trans", 3);
  rk_read(&R_rd_trans, RD(L(0), L(1)));
  rk_read(&R_rd_trans, RD(L(1), L(2)));
  rk_make(&R_rd_trans, RD(L(0), L(2)));
  rk_init(&R_rd_beta, "beta", 4); /* D0 B1 U2 R3 */
  rk_read(&R_rd_beta, EV(L(1), bl_cs(B, L(2), ID), L(3)));
  rk_make(&R_rd_beta, RD(APP(LAM(L(0), L(1)), L(2)), L(3)));
  rk_param(&R_rd_beta, 0);
  rk_init(&R_rd_delta, "delta", 2);
  rk_read(&R_rd_delta, T2(f_defn, L(0), L(1)));
  rk_make(&R_rd_delta, RD(T1(c_cst, L(0)), L(1)));
  bin_cong(&R_rd_app, "rd app", f_rd, c_app, true, true, false, false);
  bin_cong(&R_rd_lam, "rd lam", f_rd, c_lam, true, true, false, false);
  bin_cong(&R_rd_pi, "rd pi", f_rd, c_pi, true, true, false, false);
  /* conversion */
  rk_init(&R_cv_refl, "conv refl", 1);
  rk_make(&R_cv_refl, CONV(L(0), L(0)));
  rk_param(&R_cv_refl, 0);
  rk_init(&R_cv_redl, "conv reduce left", 3); /* A0 A'1 B2 */
  rk_read(&R_cv_redl, RD(L(0), L(1)));
  rk_read(&R_cv_redl, CONV(L(1), L(2)));
  rk_make(&R_cv_redl, CONV(L(0), L(2)));
  rk_init(&R_cv_redr, "conv reduce right", 3); /* A0 B1 B'2 */
  rk_read(&R_cv_redr, RD(L(1), L(2)));
  rk_read(&R_cv_redr, CONV(L(0), L(2)));
  rk_make(&R_cv_redr, CONV(L(0), L(1)));
  bin_cong(&R_cv_app, "conv app", f_conv, c_app, true, true, false, false);
  bin_cong(&R_cv_lam, "conv lam (domains ignored)", f_conv, c_lam, false, true, true, false);
  bin_cong(&R_cv_pi, "conv pi", f_conv, c_pi, FAULT != 4, true, FAULT == 4, false);
  rk_init(&R_cv_etal, "conv eta left", 4); /* D0 B1 U2 U'3 */
  rk_read(&R_cv_etal, EV(L(2), SH, L(3)));
  rk_read(&R_cv_etal, CONV(L(1), APP(L(3), VAR(0))));
  rk_make(&R_cv_etal, CONV(LAM(L(0), L(1)), L(2)));
  rk_param(&R_cv_etal, 0);
  rk_init(&R_cv_etar, "conv eta right", 4);
  rk_read(&R_cv_etar, EV(L(2), SH, L(3)));
  rk_read(&R_cv_etar, CONV(APP(L(3), VAR(0)), L(1)));
  rk_make(&R_cv_etar, CONV(L(2), LAM(L(0), L(1))));
  rk_param(&R_cv_etar, 0);
  /* typing */
  rk_init(&R_ctx_nil, "empty context", 0);
  rk_make(&R_ctx_nil, T1(f_ctx, NIL));
  for (int s = 0; s < 2; s++) {
    rk_init(&R_ctx_cons[s], "context extension", 2); /* A0 G1 */
    rk_read(&R_ctx_cons[s], T1(f_ctx, L(1)));
    rk_read(&R_ctx_cons[s], TYS(L(1), L(0), sorts[s]));
    rk_make(&R_ctx_cons[s], T1(f_ctx, CONS(L(0), L(1))));
    rk_init(&R_tys[s], "a type of a sort", 3); /* G0 A1 T2 */
    rk_read(&R_tys[s], TY(L(0), L(1), L(2)));
    rk_read(&R_tys[s], T3(f_cv, L(0), L(2), sorts[s]));
    rk_make(&R_tys[s], TYS(L(0), L(1), sorts[s]));
  }
  rk_init(&R_lookup0, "lookup 0", 3); /* A0 G1 A'2 */
  rk_read(&R_lookup0, EV(L(0), SH, L(2)));
  rk_make(&R_lookup0, T3(f_lookup, CONS(L(0), L(1)), ZERO, L(2)));
  rk_param(&R_lookup0, 1);
  rk_init(&R_lookupS, "lookup n+1", 5); /* B0 G1 N2 A3 A'4 */
  rk_read(&R_lookupS, T3(f_lookup, L(1), L(2), L(3)));
  rk_read(&R_lookupS, EV(L(3), SH, L(4)));
  rk_make(&R_lookupS, T3(f_lookup, CONS(L(0), L(1)), T1(f_s, L(2)), L(4)));
  rk_param(&R_lookupS, 0);
  rk_init(&R_ty_type, "Type : Kind", 1);
  rk_read(&R_ty_type, T1(f_ctx, L(0)));
  rk_make(&R_ty_type, TY(L(0), TYPE, KIND));
  rk_init(&R_ty_cst, "constant", 3); /* G0 K1 A2 */
  rk_read(&R_ty_cst, T1(f_ctx, L(0)));
  rk_read(&R_ty_cst, T2(f_decl, L(1), L(2)));
  rk_make(&R_ty_cst, TY(L(0), T1(c_cst, L(1)), L(2)));
  rk_init(&R_ty_var, "variable", 3); /* G0 N1 A2 */
  rk_read(&R_ty_var, T1(f_ctx, L(0)));
  rk_read(&R_ty_var, T3(f_lookup, L(0), L(1), L(2)));
  rk_make(&R_ty_var, TY(L(0), VART(L(1)), L(2)));
  for (int sd = 0; sd < 2; sd++) {
    for (int sc = 0; sc < 2; sc++) {
      rk_init(&R_ty_pi[sd][sc], "product", 3); /* G0 A1 B2 */
      rk_read(&R_ty_pi[sd][sc], TYS(L(0), L(1), sorts[sd]));
      rk_read(&R_ty_pi[sd][sc], TYS(CONS(L(1), L(0)), L(2), sorts[sc]));
      rk_make(&R_ty_pi[sd][sc], TY(L(0), PI(L(1), L(2)), sorts[sc]));
    }
    rk_init(&R_ty_lam[sd], "abstraction", 4); /* G0 A1 B2 T3 */
    rk_read(&R_ty_lam[sd], TYS(L(0), L(1), sorts[sd]));
    rk_read(&R_ty_lam[sd], TY(CONS(L(1), L(0)), L(2), L(3)));
    rk_apart(&R_ty_lam[sd], L(3), KIND);
    rk_make(&R_ty_lam[sd], TY(L(0), LAM(L(1), L(2)), PI(L(1), L(3))));
    rk_init(&R_ty_lamn[sd], "abstraction without domain", 4);
    rk_read(&R_ty_lamn[sd], TYS(L(0), L(1), sorts[sd]));
    rk_read(&R_ty_lamn[sd], TY(CONS(L(1), L(0)), L(2), L(3)));
    rk_apart(&R_ty_lamn[sd], L(3), KIND);
    rk_make(&R_ty_lamn[sd], TY(L(0), LAM(NONE, L(2)), PI(L(1), L(3))));
  }
  rk_init(&R_ty_app, "application", 8); /* G0 F1 U2 P3 A4 B5 A'6 R7 */
  rk_read(&R_ty_app, TY(L(0), L(1), L(3)));
  rk_read(&R_ty_app, T3(f_cv, L(0), L(3), PI(L(4), L(5))));
  rk_read(&R_ty_app, TY(L(0), L(2), L(6)));
  if (FAULT != 1) rk_read(&R_ty_app, T3(f_cv, L(0), L(6), L(4)));
  rk_read(&R_ty_app, EV(L(5), bl_cs(B, L(2), ID), L(7)));
  rk_make(&R_ty_app, TY(L(0), APP(L(1), L(2)), L(7)));
  /* negative judgments */
  rk_init(&R_epoch0, "the first epoch", 0);
  R_epoch0.fresh = 1;
  rk_make(&R_epoch0, T1(f_epoch, tr_fresh(C, 0)));
  rk_init(&R_head_var, "head of a variable", 1);
  rk_make(&R_head_var, T3(f_head, VART(L(0)), VART(L(0)), ZERO));
  rk_param(&R_head_var, 0);
  rk_init(&R_head_cst, "head of a constant", 1);
  rk_make(&R_head_cst, T3(f_head, T1(c_cst, L(0)), T1(c_cst, L(0)), ZERO));
  rk_param(&R_head_cst, 0);
  rk_init(&R_head_app, "head of an application", 4); /* A0 B1 H2 N3 */
  rk_read(&R_head_app, T3(f_head, L(0), L(2), L(3)));
  rk_make(&R_head_app, T3(f_head, APP(L(0), L(1)), L(2), T1(f_s, L(3))));
  rk_param(&R_head_app, 1);
  tr_term leaves[3] = {TYPE, KIND, NONE}, lshape[3] = {T0(f_st), T0(f_sk), T0(f_sn)};
  for (int i = 0; i < 3; i++) {
    rk_init(&R_hn_leaf[i], "whnf of a sort", 1);
    rk_read(&R_hn_leaf[i], T1(f_epoch, L(0)));
    rk_make(&R_hn_leaf[i], T2(f_hn, leaves[i], L(0)));
    rk_init(&R_nfw_leaf[i], "normal sort", 1);
    rk_read(&R_nfw_leaf[i], T1(f_epoch, L(0)));
    rk_make(&R_nfw_leaf[i], T3(f_nfw, leaves[i], leaves[i], L(0)));
    rk_init(&R_shape_leaf[i], "shape of a sort", 0);
    rk_make(&R_shape_leaf[i], T2(f_shape, leaves[i], lshape[i]));
  }
  rk_init(&R_hn_pi, "whnf of a product", 3);
  rk_read(&R_hn_pi, T1(f_epoch, L(2)));
  rk_make(&R_hn_pi, T2(f_hn, PI(L(0), L(1)), L(2)));
  rk_param(&R_hn_pi, 0), rk_param(&R_hn_pi, 1);
  rk_init(&R_hn_lam, "whnf of an abstraction", 3);
  rk_read(&R_hn_lam, T1(f_epoch, L(2)));
  rk_make(&R_hn_lam, T2(f_hn, LAM(L(0), L(1)), L(2)));
  rk_param(&R_hn_lam, 0), rk_param(&R_hn_lam, 1);
  rk_init(&R_hn_var, "whnf: a variable head", 4); /* W0 K1 N2 E3 */
  rk_read(&R_hn_var, T3(f_head, L(0), VART(L(1)), L(2)));
  rk_read(&R_hn_var, T1(f_epoch, L(3)));
  rk_make(&R_hn_var, T2(f_hn, L(0), L(3)));
  rk_init(&R_hn_static, "whnf: a static head", 4);
  rk_read(&R_hn_static, T3(f_head, L(0), T1(c_cst, L(1)), L(2)));
  rk_read(&R_hn_static, T1(f_static, L(1)));
  rk_read(&R_hn_static, T1(f_epoch, L(3)));
  rk_make(&R_hn_static, T2(f_hn, L(0), L(3)));
  rk_init(&R_hn_def, "whnf: no rule of the head matches", 5); /* W0 K1 N2 L3 E4 */
  rk_read(&R_hn_def, T3(f_head, L(0), T1(c_cst, L(1)), L(2)));
  rk_read(&R_hn_def, T2(f_rules, L(1), L(3)));
  rk_read(&R_hn_def, T4(f_nmall, L(0), L(2), L(3), L(4)));
  rk_make(&R_hn_def, T2(f_hn, L(0), L(4)));
  rk_init(&R_nmall_nil, "no rule of none", 3); /* W0 N1 E2 */
  rk_read(&R_nmall_nil, T1(f_epoch, L(2)));
  rk_make(&R_nmall_nil, T4(f_nmall, L(0), L(1), NIL, L(2)));
  rk_param(&R_nmall_nil, 0), rk_param(&R_nmall_nil, 1);
  rk_init(&R_nmall_nm, "one more rule that does not match", 6); /* W0 N1 R2 K3 L4 E5 */
  rk_read(&R_nmall_nm, T4(f_nmall, L(0), L(1), L(4), L(5)));
  rk_read(&R_nmall_nm, T3(f_nomatch, L(2), L(0), L(5)));
  rk_make(&R_nmall_nm, T4(f_nmall, L(0), L(1), CONS(T2(f_rl, L(2), L(3)), L(4)), L(5)));
  rk_param(&R_nmall_nm, 3);
  rk_init(&R_nmall_short, "one more rule with more arguments", 6);
  rk_read(&R_nmall_short, T4(f_nmall, L(0), L(1), L(4), L(5)));
  rk_read(&R_nmall_short, T2(f_lt, L(1), L(3)));
  rk_make(&R_nmall_short, T4(f_nmall, L(0), L(1), CONS(T2(f_rl, L(2), L(3)), L(4)), L(5)));
  rk_param(&R_nmall_short, 2);
  rk_init(&R_nm_lift, "no match on a prefix", 4); /* R0 W1 B2 E3 */
  rk_read(&R_nm_lift, T3(f_nomatch, L(0), L(1), L(3)));
  rk_make(&R_nm_lift, T3(f_nomatch, L(0), APP(L(1), L(2)), L(3)));
  rk_param(&R_nm_lift, 2);
  rk_init(&R_lt0, "0 < k+1", 1);
  rk_make(&R_lt0, T2(f_lt, ZERO, T1(f_s, L(0))));
  rk_param(&R_lt0, 0);
  rk_init(&R_ltS, "n+1 < k+1", 2);
  rk_read(&R_ltS, T2(f_lt, L(0), L(1)));
  rk_make(&R_ltS, T2(f_lt, T1(f_s, L(0)), T1(f_s, L(1))));
  rk_init(&R_wh, "weak head normal form", 3); /* A0 W1 E2 */
  rk_read(&R_wh, RD(L(0), L(1)));
  rk_read(&R_wh, T2(f_hn, L(1), L(2)));
  rk_make(&R_wh, WH(L(0), L(1), L(2)));
  rk_init(&R_nf, "normal form", 4); /* A0 W1 N2 E3 */
  rk_read(&R_nf, WH(L(0), L(1), L(3)));
  rk_read(&R_nf, T3(f_nfw, L(1), L(2), L(3)));
  rk_make(&R_nf, T3(f_nf, L(0), L(2), L(3)));
  rk_init(&R_nfw_var, "normal variable", 2);
  rk_read(&R_nfw_var, T1(f_epoch, L(1)));
  rk_make(&R_nfw_var, T3(f_nfw, VART(L(0)), VART(L(0)), L(1)));
  rk_param(&R_nfw_var, 0);
  rk_init(&R_nfw_cst, "normal constant", 2);
  rk_read(&R_nfw_cst, T1(f_epoch, L(1)));
  rk_make(&R_nfw_cst, T3(f_nfw, T1(c_cst, L(0)), T1(c_cst, L(0)), L(1)));
  rk_param(&R_nfw_cst, 0);
  rk_init(&R_nfw_app, "normal application", 5); /* A0 B1 A'2 B'3 E4 */
  rk_read(&R_nfw_app, T3(f_nfw, L(0), L(2), L(4)));
  rk_read(&R_nfw_app, T3(f_nf, L(1), L(3), L(4)));
  rk_make(&R_nfw_app, T3(f_nfw, APP(L(0), L(1)), APP(L(2), L(3)), L(4)));
  rk_init(&R_nfw_lam, "normal abstraction", 5);
  rk_read(&R_nfw_lam, T3(f_nf, L(0), L(2), L(4)));
  rk_read(&R_nfw_lam, T3(f_nf, L(1), L(3), L(4)));
  rk_make(&R_nfw_lam, T3(f_nfw, LAM(L(0), L(1)), LAM(L(2), L(3)), L(4)));
  rk_init(&R_nfw_pi, "normal product", 5);
  rk_read(&R_nfw_pi, T3(f_nf, L(0), L(2), L(4)));
  rk_read(&R_nfw_pi, T3(f_nf, L(1), L(3), L(4)));
  rk_make(&R_nfw_pi, T3(f_nfw, PI(L(0), L(1)), PI(L(2), L(3)), L(4)));
  rk_init(&R_shape_pi, "shape of a product", 2);
  rk_make(&R_shape_pi, T2(f_shape, PI(L(0), L(1)), T0(f_sp)));
  rk_param(&R_shape_pi, 0), rk_param(&R_shape_pi, 1);
  rk_init(&R_shape_lam, "shape of an abstraction", 2);
  rk_make(&R_shape_lam, T2(f_shape, LAM(L(0), L(1)), SL));
  rk_param(&R_shape_lam, 0), rk_param(&R_shape_lam, 1);
  rk_init(&R_shape_var, "shape of a variable spine", 3); /* W0 K1 N2 */
  rk_read(&R_shape_var, T3(f_head, L(0), VART(L(1)), L(2)));
  rk_make(&R_shape_var, T2(f_shape, L(0), T2(f_sv, L(1), L(2))));
  rk_init(&R_shape_cst, "shape of a constant spine", 3);
  rk_read(&R_shape_cst, T3(f_head, L(0), T1(c_cst, L(1)), L(2)));
  rk_make(&R_shape_cst, T2(f_shape, L(0), T2(f_sc, L(1), L(2))));
  rk_init(&R_nc_shape, "different shapes", 5); /* W0 W1 S2 S3 E4 */
  rk_read(&R_nc_shape, T2(f_shape, L(0), L(2)));
  rk_read(&R_nc_shape, T2(f_shape, L(1), L(3)));
  rk_read(&R_nc_shape, T1(f_epoch, L(4)));
  rk_apart(&R_nc_shape, L(2), L(3));
  if (ETA) rk_apart(&R_nc_shape, L(2), SL), rk_apart(&R_nc_shape, L(3), SL);
  rk_make(&R_nc_shape, T3(f_nc, L(0), L(1), L(4)));
  rk_init(&R_nc_appf, "different spines", 5); /* A0 B1 A'2 B'3 E4 */
  rk_read(&R_nc_appf, T3(f_nc, L(0), L(2), L(4)));
  rk_make(&R_nc_appf, T3(f_nc, APP(L(0), L(1)), APP(L(2), L(3)), L(4)));
  rk_param(&R_nc_appf, 1), rk_param(&R_nc_appf, 3);
  rk_init(&R_nc_appa, "different arguments", 5);
  rk_read(&R_nc_appa, T3(f_notconv, L(1), L(3), L(4)));
  rk_make(&R_nc_appa, T3(f_nc, APP(L(0), L(1)), APP(L(2), L(3)), L(4)));
  rk_param(&R_nc_appa, 0), rk_param(&R_nc_appa, 2);
  rk_init(&R_nc_lam, "different bodies", 5);
  rk_read(&R_nc_lam, T3(f_notconv, L(1), L(3), L(4)));
  rk_make(&R_nc_lam, T3(f_nc, LAM(L(0), L(1)), LAM(L(2), L(3)), L(4)));
  rk_param(&R_nc_lam, 0), rk_param(&R_nc_lam, 2);
  rk_init(&R_nc_pid, "different domains", 5);
  rk_read(&R_nc_pid, T3(f_notconv, L(0), L(2), L(4)));
  rk_make(&R_nc_pid, T3(f_nc, PI(L(0), L(1)), PI(L(2), L(3)), L(4)));
  rk_param(&R_nc_pid, 1), rk_param(&R_nc_pid, 3);
  rk_init(&R_nc_pic, "different codomains", 5);
  rk_read(&R_nc_pic, T3(f_notconv, L(1), L(3), L(4)));
  rk_make(&R_nc_pic, T3(f_nc, PI(L(0), L(1)), PI(L(2), L(3)), L(4)));
  rk_param(&R_nc_pic, 0), rk_param(&R_nc_pic, 2);
  rk_init(&R_nc_etal, "eta: different", 6); /* D0 B1 W2 W'3 S4 E5 */
  rk_read(&R_nc_etal, T2(f_shape, L(2), L(4)));
  rk_read(&R_nc_etal, EV(L(2), SH, L(3)));
  rk_read(&R_nc_etal, T3(f_notconv, L(1), APP(L(3), VAR(0)), L(5)));
  rk_apart(&R_nc_etal, L(4), SL);
  rk_make(&R_nc_etal, T3(f_nc, LAM(L(0), L(1)), L(2), L(5)));
  rk_param(&R_nc_etal, 0);
  rk_init(&R_nc_etar, "eta: different", 6);
  rk_read(&R_nc_etar, T2(f_shape, L(2), L(4)));
  rk_read(&R_nc_etar, EV(L(2), SH, L(3)));
  rk_read(&R_nc_etar, T3(f_notconv, APP(L(3), VAR(0)), L(1), L(5)));
  rk_apart(&R_nc_etar, L(4), SL);
  rk_make(&R_nc_etar, T3(f_nc, L(2), LAM(L(0), L(1)), L(5)));
  rk_param(&R_nc_etar, 0);
  /* hypotheses */
  rk_init(&R_ctx_hyp, "a context with a hypothesis", 3); /* X0 Y1 G2 */
  rk_read(&R_ctx_hyp, T1(f_ctx, L(2)));
  rk_make(&R_ctx_hyp, T1(f_ctx, T3(f_hyp, L(0), L(1), L(2))));
  rk_param(&R_ctx_hyp, 0), rk_param(&R_ctx_hyp, 1);
  rk_init(&R_lookup_hyp, "lookup past a hypothesis", 5); /* X0 Y1 G2 N3 A4 */
  rk_read(&R_lookup_hyp, T3(f_lookup, L(2), L(3), L(4)));
  rk_make(&R_lookup_hyp, T3(f_lookup, T3(f_hyp, L(0), L(1), L(2)), L(3), L(4)));
  rk_param(&R_lookup_hyp, 0), rk_param(&R_lookup_hyp, 1);
  rk_init(&R_cv_conv, "convertible, hence under any hypotheses", 3); /* G0 X1 Y2 */
  rk_read(&R_cv_conv, CONV(L(1), L(2)));
  rk_make(&R_cv_conv, T3(f_cv, L(0), L(1), L(2)));
  rk_param(&R_cv_conv, 0);
  rk_init(&R_cv_hyp, "a hypothesis", 3);
  rk_make(&R_cv_hyp, T3(f_cv, T3(f_hyp, L(0), L(1), L(2)), L(0), L(1)));
  rk_param(&R_cv_hyp, 0), rk_param(&R_cv_hyp, 1), rk_param(&R_cv_hyp, 2);
  rk_init(&R_cv_sym, "symmetry under hypotheses", 3);
  rk_read(&R_cv_sym, T3(f_cv, L(0), L(1), L(2)));
  rk_make(&R_cv_sym, T3(f_cv, L(0), L(2), L(1)));
  rk_init(&R_cv_trans, "transitivity under hypotheses", 4);
  rk_read(&R_cv_trans, T3(f_cv, L(0), L(1), L(2)));
  rk_read(&R_cv_trans, T3(f_cv, L(0), L(2), L(3)));
  rk_make(&R_cv_trans, T3(f_cv, L(0), L(1), L(3)));
  rk_init(&R_cv_wk_hyp, "weakening by a hypothesis", 5); /* X0 Y1 G2 A3 B4 */
  rk_read(&R_cv_wk_hyp, T3(f_cv, L(2), L(3), L(4)));
  rk_make(&R_cv_wk_hyp, T3(f_cv, T3(f_hyp, L(0), L(1), L(2)), L(3), L(4)));
  rk_param(&R_cv_wk_hyp, 0), rk_param(&R_cv_wk_hyp, 1);
  rk_init(&R_cv_wk_cons, "weakening by a binder", 6); /* D0 G1 A2 B3 A'4 B'5 */
  rk_read(&R_cv_wk_cons, T3(f_cv, L(1), L(2), L(3)));
  rk_read(&R_cv_wk_cons, EV(L(2), SH, L(4)));
  rk_read(&R_cv_wk_cons, EV(L(3), SH, L(5)));
  rk_make(&R_cv_wk_cons, T3(f_cv, CONS(L(0), L(1)), L(4), L(5)));
  rk_param(&R_cv_wk_cons, 0);
  rk_init(&R_cvh_app, "congruence under hypotheses", 5); /* G0 A1 B2 A'3 B'4 */
  rk_read(&R_cvh_app, T3(f_cv, L(0), L(1), L(3)));
  rk_read(&R_cvh_app, T3(f_cv, L(0), L(2), L(4)));
  rk_make(&R_cvh_app, T3(f_cv, L(0), APP(L(1), L(2)), APP(L(3), L(4))));
  rk_init(&R_cvh_pi, "product congruence under hypotheses", 5); /* G0 A1 B2 A'3 B'4 */
  rk_read(&R_cvh_pi, T3(f_cv, L(0), L(1), L(3)));
  rk_read(&R_cvh_pi, T3(f_cv, CONS(L(1), L(0)), L(2), L(4)));
  rk_make(&R_cvh_pi, T3(f_cv, L(0), PI(L(1), L(2)), PI(L(3), L(4))));
  rk_init(&R_cvh_lam, "abstraction congruence under hypotheses (domains ignored)", 5); /* G0 D1 B2 D'3 B'4 */
  rk_read(&R_cvh_lam, T3(f_cv, CONS(L(1), L(0)), L(2), L(4)));
  rk_make(&R_cvh_lam, T3(f_cv, L(0), LAM(L(1), L(2)), LAM(L(3), L(4))));
  rk_param(&R_cvh_lam, 3);
  rk_init(&R_cv_red, "reduction under hypotheses", 4); /* G0 X1 X'2 Y3 */
  rk_read(&R_cv_red, RD(L(1), L(2)));
  rk_read(&R_cv_red, T3(f_cv, L(0), L(2), L(3)));
  rk_make(&R_cv_red, T3(f_cv, L(0), L(1), L(3)));
  /* a static head is injective (under confluence, Dedukti's own assumption): from F A == F' A'
   * with F, F' spines of one static symbol and of one length, A == A' and F == F'.  (A variable
   * head is not: here every variable is a pattern variable, which an instance may replace.) */
  for (int inj = 0; inj < 2; inj++)
    for (int part = 0; part < 2; part++) { /* G0 F1 A2 F'3 A'4 K5 N6 */
      rk_rule *r = &R_cv_dec[inj][part];
      rk_init(r, inj ? "injectivity of a symbol declared injective" : "injectivity of a static head", 7);
      rk_read(r, T3(f_cv, L(0), APP(L(1), L(2)), APP(L(3), L(4))));
      rk_read(r, T3(f_head, L(1), T1(c_cst, L(5)), L(6)));
      rk_read(r, T3(f_head, L(3), T1(c_cst, L(5)), L(6)));
      rk_read(r, T1(inj ? f_inj : f_static, L(5)));
      rk_make(r, part ? T3(f_cv, L(0), L(1), L(3)) : T3(f_cv, L(0), L(2), L(4)));
    }
  rk_init(&R_sub_refl, "a term is its own subterm", 1);
  rk_make(&R_sub_refl, T2(f_sub, L(0), L(0)));
  rk_param(&R_sub_refl, 0);
  rk_init(&R_sub_fun, "the function of an application subterm", 3);
  rk_read(&R_sub_fun, T2(f_sub, L(0), APP(L(1), L(2))));
  rk_make(&R_sub_fun, T2(f_sub, L(0), L(1)));
  rk_init(&R_sub_arg, "the argument of an application subterm", 3);
  rk_read(&R_sub_arg, T2(f_sub, L(0), APP(L(1), L(2))));
  rk_make(&R_sub_arg, T2(f_sub, L(0), L(2)));
  /* An obligation is a conversion between two types that every typable instance determines: F
   * and U are headed by constants, so the type of F and the type of U are their declared types
   * instantiated (uniqueness of types, under the hypotheses already admitted).  Where a pattern
   * variable is the head, its type is the one its context entry gives, which an instance need
   * not respect (an annotation, or a proposal): no obligation is made there. */
  rk_init(&R_oblig, "a conversion every typable instance needs", 12); /* G0 L1 F2 U3 P4 A5 B6 X7 HF8 NF9 HU10 NU11 */
  rk_read(&R_oblig, T2(f_sub, L(1), APP(L(2), L(3))));
  rk_read(&R_oblig, TY(L(0), L(2), L(4)));
  rk_read(&R_oblig, T3(f_cv, L(0), L(4), PI(L(5), L(6))));
  rk_read(&R_oblig, TY(L(0), L(3), L(7)));
  rk_read(&R_oblig, T3(f_head, L(2), T1(c_cst, L(8)), L(9)));
  rk_read(&R_oblig, T3(f_head, L(3), T1(c_cst, L(10)), L(11)));
  rk_make(&R_oblig, T4(f_oblig, L(0), L(1), L(7), L(5)));
  /* pin(G, L, N): the type of var(N) in G is the type that a position of var(N) in L imposes, the
   * argument of a constant-headed F (outside binders and brackets, as sub goes): every typable
   * instance gives the variable F's domain, which G's type of it is convertible to.  A pinned
   * variable's type is then determined like a constant's, and an obligation may be made at another
   * of its positions (a variable used at two positions whose types must agree). */
  rk_init(&R_pin, "a variable's type pinned by a position", 10); /* G0 L1 F2 N3 P4 A5 B6 X7 H8 K9 */
  rk_read(&R_pin, T2(f_sub, L(1), APP(L(2), VART(L(3)))));
  rk_read(&R_pin, T3(f_head, L(2), T1(c_cst, L(8)), L(9)));
  rk_read(&R_pin, TY(L(0), L(2), L(4)));
  rk_read(&R_pin, T3(f_cv, L(0), L(4), PI(L(5), L(6))));
  rk_read(&R_pin, TY(L(0), VART(L(3)), L(7)));
  rk_read(&R_pin, T3(f_cv, L(0), L(7), L(5)));
  rk_make(&R_pin, T3(f_pin, L(0), L(1), L(3)));
  rk_init(&R_oblig_var, "a conversion every typable instance needs, at a pinned variable", 10);
  /* G0 L1 F2 N3 P4 A5 B6 X7 H8 K9 */
  rk_read(&R_oblig_var, T2(f_sub, L(1), APP(L(2), VART(L(3)))));
  rk_read(&R_oblig_var, T3(f_head, L(2), T1(c_cst, L(8)), L(9)));
  rk_read(&R_oblig_var, TY(L(0), L(2), L(4)));
  rk_read(&R_oblig_var, T3(f_cv, L(0), L(4), PI(L(5), L(6))));
  rk_read(&R_oblig_var, TY(L(0), VART(L(3)), L(7)));
  rk_read(&R_oblig_var, T3(f_pin, L(0), L(1), L(3)));
  rk_make(&R_oblig_var, T4(f_oblig, L(0), L(1), L(7), L(5)));
  /* Under a pattern abstraction F (x => B), checked against F's domain pi(D, C): the body's type T
   * (in cons(D, G)) is C in every typable instance (product injectivity), and an obligation X == A
   * of the body is one of the abstraction; both are stated abstracted, x => T == x => C, which is
   * the same equation with x free (abstraction congruence one way, application to x and beta the
   * other). */
  /* F : pi(pi(D, C), E) */
  rk_init(&R_oblig_lamty, "a pattern abstraction's body has the expected type", 14);
  /* G0 L1 F2 N3 B4 P5 D6 C7 T8 E9 HF10 NF11 HB12 NB13 */
  rk_read(&R_oblig_lamty, T2(f_sub, L(1), APP(L(2), LAM(L(3), L(4)))));
  rk_read(&R_oblig_lamty, TY(L(0), L(2), L(5)));
  rk_read(&R_oblig_lamty, T3(f_cv, L(0), L(5), PI(PI(L(6), L(7)), L(9))));
  rk_read(&R_oblig_lamty, TY(CONS(L(6), L(0)), L(4), L(8)));
  rk_read(&R_oblig_lamty, T3(f_head, L(2), T1(c_cst, L(10)), L(11)));
  rk_read(&R_oblig_lamty, T3(f_head, L(4), T1(c_cst, L(12)), L(13)));
  rk_make(&R_oblig_lamty, T4(f_oblig, L(0), L(1), LAM(NONE, L(8)), LAM(NONE, L(7))));
  /* just(L, K, G): every hypothesis of G is justified as an obligation of the left-hand side L,
   * where G is a tail of L's context with K variable entries above it.  A hypothesis X == A over G
   * is justified by oblig(G, S, X, A) for a term S over G's variables which, weakened past those K
   * entries, is a subterm of L outside its binders (every typable instance of L has S's instance
   * typable).  The admission reads just(L, 0, context): no hypothesis goes unjustified. */
  rk_init(&R_just_nil, "no hypothesis in the empty context", 2); /* L0 K1 */
  rk_make(&R_just_nil, T3(f_just, L(0), L(1), NIL));
  rk_param(&R_just_nil, 0), rk_param(&R_just_nil, 1);
  rk_init(&R_just_cons, "a variable entry needs no justification", 4); /* L0 K1 G2 T3 */
  rk_read(&R_just_cons, T3(f_just, L(0), T1(f_s, L(1)), L(2)));
  rk_make(&R_just_cons, T3(f_just, L(0), L(1), CONS(L(3), L(2))));
  rk_param(&R_just_cons, 3);
  rk_init(&R_just_hyp, "a hypothesis justified by an obligation", 7); /* L0 K1 G2 S3 X4 A5 F6 */
  rk_read(&R_just_hyp, T3(f_just, L(0), L(1), L(2)));
  rk_read(&R_just_hyp, T4(f_oblig, L(2), L(3), L(4), L(5)));
  rk_read(&R_just_hyp, T2(f_sub, L(0), L(6)));
  rk_read(&R_just_hyp, EV(L(3), T1(f_shk, L(1)), L(6)));
  rk_make(&R_just_hyp, T3(f_just, L(0), L(1), T3(f_hyp, L(4), L(5), L(2))));
  rk_init(&R_oblig_lam, "an obligation inside a pattern abstraction", 13); /* G0 L1 F2 N3 B4 P5 D6 C7 X8 A9 E10 HF11 NF12 */
  rk_read(&R_oblig_lam, T2(f_sub, L(1), APP(L(2), LAM(L(3), L(4)))));
  rk_read(&R_oblig_lam, TY(L(0), L(2), L(5)));
  rk_read(&R_oblig_lam, T3(f_cv, L(0), L(5), PI(PI(L(6), L(7)), L(10))));
  rk_read(&R_oblig_lam, T4(f_oblig, CONS(L(6), L(0)), L(4), L(8), L(9)));
  rk_read(&R_oblig_lam, T3(f_head, L(2), T1(c_cst, L(11)), L(12)));
  rk_make(&R_oblig_lam, T4(f_oblig, L(0), L(1), LAM(NONE, L(8)), LAM(NONE, L(9))));
  /* Refutations of a context's hypotheses.  A static symbol takes no rules in any safe extension
   * (confluent, rules only for definable symbols: Saillard, thesis 3.6), so an application headed
   * by one is never rewritten at its head: its reducts are its arguments' reducts in place, and two
   * terms with different rigid tops are never convertible (confluence). */
  rk_init(&R_rocc_here, "a variable as an argument of a static spine", 4); /* F0 N1 K2 M3 */
  rk_read(&R_rocc_here, T3(f_head, APP(L(0), VART(L(1))), T1(c_cst, L(2)), L(3)));
  if (FAULT != 6) rk_read(&R_rocc_here, T1(f_static, L(2)));
  rk_make(&R_rocc_here, T2(f_rocc, VART(L(1)), APP(L(0), VART(L(1)))));
  rk_init(&R_rocc_arg, "a variable inside an argument of a static spine", 5); /* F0 A1 K2 M3 V4 */
  rk_read(&R_rocc_arg, T3(f_head, APP(L(0), L(1)), T1(c_cst, L(2)), L(3)));
  if (FAULT != 6) rk_read(&R_rocc_arg, T1(f_static, L(2)));
  rk_read(&R_rocc_arg, T2(f_rocc, L(4), L(1)));
  rk_make(&R_rocc_arg, T2(f_rocc, L(4), APP(L(0), L(1))));
  rk_init(&R_rocc_fun, "a variable inside an earlier argument of a static spine", 5); /* F0 A1 K2 M3 V4 */
  rk_read(&R_rocc_fun, T3(f_head, APP(L(0), L(1)), T1(c_cst, L(2)), L(3)));
  if (FAULT != 6) rk_read(&R_rocc_fun, T1(f_static, L(2)));
  rk_read(&R_rocc_fun, T2(f_rocc, L(4), L(0)));
  rk_make(&R_rocc_fun, T2(f_rocc, L(4), APP(L(0), L(1))));
  rk_init(&R_rshape_cst, "a static spine is rigid", 3); /* T0 K1 N2 */
  rk_read(&R_rshape_cst, T3(f_head, L(0), T1(c_cst, L(1)), L(2)));
  if (FAULT != 6) rk_read(&R_rshape_cst, T1(f_static, L(1)));
  rk_make(&R_rshape_cst, T2(f_rshape, L(0), T2(f_sc, L(1), L(2))));
  rk_init(&R_rshape_pi, "a product is rigid", 2);
  rk_make(&R_rshape_pi, T2(f_rshape, PI(L(0), L(1)), T0(f_sp)));
  rk_param(&R_rshape_pi, 0), rk_param(&R_rshape_pi, 1);
  rk_init(&R_rshape_sort[0], "Type is rigid", 0);
  rk_make(&R_rshape_sort[0], T2(f_rshape, TYPE, T0(f_st)));
  rk_init(&R_rshape_sort[1], "Kind is rigid", 0);
  rk_make(&R_rshape_sort[1], T2(f_rshape, KIND, T0(f_sk)));
  /* cv(G, X, Y) holds in every solution of G's hypotheses; with different rigid tops it holds in
   * none, so there is no solution (and no typable instance of the left-hand side) */
  rk_init(&R_nosol, "hypotheses with no solution", 5); /* G0 X1 Y2 S3 S'4 */
  rk_read(&R_nosol, T3(f_cv, L(0), L(1), L(2)));
  rk_read(&R_nosol, T2(f_rshape, L(1), L(3)));
  rk_read(&R_nosol, T2(f_rshape, L(2), L(4)));
  rk_apart(&R_nosol, L(3), L(4));
  rk_make(&R_nosol, T3(f_nosol, L(0), L(1), L(2)));
  /* cv(G, V, T) with V inside T along static heads: if V's instance had a normal form N, T's
   * instance would reduce to N (confluence) and N would contain, below its top, a reduct of V's
   * instance, i.e. N itself.  So no solution gives V an instance with a normal form. */
  rk_init(&R_nowf, "hypotheses with no well-founded solution", 3); /* G0 V1 T2 */
  rk_read(&R_nowf, T3(f_cv, L(0), L(1), L(2)));
  rk_read(&R_nowf, T2(f_rocc, L(1), L(2)));
  rk_make(&R_nowf, T3(f_nowf, L(0), L(1), L(2)));
  /* Obligations through nested pattern abstractions (checking mode).  A constant-headed U has, in
   * every typable instance, the type its typing gives (its declared type instantiated: uniqueness
   * of types), so where it is checked against A, T == A.  An abstraction typable at a type
   * convertible to pi(D, C) has its body typable, under a binder whose type is convertible to D,
   * at a type convertible to C (product compatibility): the body's equation holds under the binder,
   * stated abstracted (x => X == x => Y, the same equation with x free). */
  rk_init(&R_obchk_cst, "a constant-headed term checked against a type", 6); /* G0 U1 A2 T3 K4 N5 */
  rk_read(&R_obchk_cst, TY(L(0), L(1), L(3)));
  rk_read(&R_obchk_cst, T3(f_head, L(1), T1(c_cst, L(4)), L(5)));
  rk_make(&R_obchk_cst, T5(f_obchk, L(0), L(1), L(2), L(3), L(2)));
  rk_param(&R_obchk_cst, 2);
  rk_init(&R_obchk_lam, "an abstraction checked against a product", 8); /* G0 N1 B2 A3 D4 C5 X6 Y7 */
  rk_read(&R_obchk_lam, T3(f_cv, L(0), L(3), PI(L(4), L(5))));
  rk_read(&R_obchk_lam, T5(f_obchk, CONS(L(4), L(0)), L(2), L(5), L(6), L(7)));
  rk_make(&R_obchk_lam, T5(f_obchk, L(0), LAM(L(1), L(2)), L(3), LAM(NONE, L(6)), LAM(NONE, L(7))));
  rk_param(&R_obchk_lam, 1);
  /* at an application F U of the left-hand side (outside binders) with F constant-headed: U is
   * checked against F's domain in every typable instance */
  rk_init(&R_oblig_chk, "a conversion every typable instance needs, at a checked argument", 11);
  /* G0 L1 F2 U3 P4 A5 E6 X7 Y8 K9 N10 */
  rk_read(&R_oblig_chk, T2(f_sub, L(1), APP(L(2), L(3))));
  rk_read(&R_oblig_chk, TY(L(0), L(2), L(4)));
  rk_read(&R_oblig_chk, T3(f_cv, L(0), L(4), PI(L(5), L(6))));
  rk_read(&R_oblig_chk, T3(f_head, L(2), T1(c_cst, L(9)), L(10)));
  rk_read(&R_oblig_chk, T5(f_obchk, L(0), L(3), L(5), L(7), L(8)));
  rk_make(&R_oblig_chk, T4(f_oblig, L(0), L(1), L(7), L(8)));
  /* rocc through an abstraction (its reducts are abstractions of its body's reducts; an eta step
   * drops only the binder): V inside x => B when V's shift is inside B, or is B */
  rk_init(&R_rocc_lam, "a variable inside an abstraction's body", 4); /* V0 V'1 B2 D3 */
  rk_read(&R_rocc_lam, EV(L(0), SH, L(1)));
  rk_read(&R_rocc_lam, T2(f_rocc, L(1), L(2)));
  rk_make(&R_rocc_lam, T2(f_rocc, L(0), LAM(L(3), L(2))));
  rk_param(&R_rocc_lam, 3);
  rk_init(&R_rocc_lam_here, "a variable as an abstraction's body", 3); /* V0 V'1 D2 */
  rk_read(&R_rocc_lam_here, EV(VART(L(0)), SH, L(1)));
  rk_make(&R_rocc_lam_here, T2(f_rocc, VART(L(0)), LAM(L(2), L(1))));
  rk_param(&R_rocc_lam_here, 2);
  /* the binder var(0) of cons(D, G) against a term that cannot mention it (a shift) */
  rk_init(&R_nosol_bindv, "a bound variable equal to a term without it", 4); /* D0 G1 V2 V'3 */
  rk_read(&R_nosol_bindv, T3(f_cv, CONS(L(0), L(1)), VAR(0), L(2)));
  rk_read(&R_nosol_bindv, EV(L(3), SH, L(2)));
  rk_make(&R_nosol_bindv, T3(f_nosol, L(1), LAM(L(0), VAR(0)), LAM(L(0), L(2))));
  rk_init(&R_nosol_bindo, "a term with a bound variable inside equal to a term without it", 5); /* D0 G1 U2 V3 V'4 */
  rk_read(&R_nosol_bindo, T3(f_cv, CONS(L(0), L(1)), L(2), L(3)));
  rk_read(&R_nosol_bindo, T2(f_rocc, VAR(0), L(2)));
  rk_read(&R_nosol_bindo, EV(L(4), SH, L(3)));
  rk_make(&R_nosol_bindo, T3(f_nosol, L(1), LAM(L(0), L(2)), LAM(L(0), L(3))));
  /* Type == Y with Y constant-headed, of a type convertible to Type: Y's type is its declared type
   * instantiated in every instance, and an instance convertible to Type would have both Type and
   * Kind (Type's type) as types; the two sorts are not convertible (uniqueness of types, subject
   * reduction and confluence: Dedukti's standing assumptions) */
  rk_init(&R_nosol_sort, "Type equal to a term of type Type", 5); /* G0 Y1 T2 K3 N4 */
  rk_read(&R_nosol_sort, T3(f_cv, L(0), TYPE, L(1)));
  rk_read(&R_nosol_sort, TY(L(0), L(1), L(2)));
  rk_read(&R_nosol_sort, T3(f_cv, L(0), L(2), TYPE));
  rk_read(&R_nosol_sort, T3(f_head, L(1), T1(c_cst, L(3)), L(4)));
  rk_make(&R_nosol_sort, T3(f_nosol, L(0), TYPE, L(1)));
  rk_init(&R_nosol_up, "no solution under a binder, none outside", 4); /* D0 G1 X2 Y3 */
  rk_read(&R_nosol_up, T3(f_nosol, CONS(L(0), L(1)), L(2), L(3)));
  rk_make(&R_nosol_up, T3(f_nosol, L(1), LAM(L(0), L(2)), LAM(L(0), L(3))));
  rk_init(&R_notconv, "not convertible", 5); /* A0 B1 W2 W'3 E4 */
  rk_read(&R_notconv, WH(L(0), L(2), L(4)));
  rk_read(&R_notconv, WH(L(1), L(3), L(4)));
  rk_read(&R_notconv, T3(f_nc, L(2), L(3), L(4)));
  rk_make(&R_notconv, T3(f_notconv, L(0), L(1), L(4)));
}

/* Every fixed rule (this file's and the binder layer's), in a fixed order: the rules the
 * specializer compiles (--emit-tcs writes them as schemas; a DK_SPEC build links the code). */
static size_t all_rules(rk_rule **out, size_t cap) {
  rk_rule *mine[] = {&R_rd_refl, &R_rd_trans, &R_rd_beta, &R_rd_delta, &R_rd_app, &R_rd_lam, &R_rd_pi, &R_cv_refl,
                     &R_cv_redl, &R_cv_redr, &R_cv_app, &R_cv_lam, &R_cv_pi, &R_cv_etal, &R_cv_etar, &R_ctx_nil,
                     &R_ctx_cons[0], &R_ctx_cons[1], &R_lookup0, &R_lookupS, &R_ty_type, &R_ty_cst, &R_ty_var,
                     &R_tys[0], &R_tys[1], &R_ty_pi[0][0], &R_ty_pi[0][1], &R_ty_pi[1][0], &R_ty_pi[1][1],
                     &R_ty_lam[0], &R_ty_lam[1], &R_ty_lamn[0], &R_ty_lamn[1], &R_ty_app, &R_ctx_hyp, &R_lookup_hyp,
                     &R_cv_conv, &R_cv_hyp, &R_cv_sym, &R_cv_trans, &R_cv_wk_hyp, &R_cv_wk_cons, &R_cvh_app,
                     &R_cvh_pi, &R_cvh_lam, &R_cv_red, &R_cv_dec[0][0], &R_cv_dec[0][1], &R_cv_dec[1][0],
                     &R_cv_dec[1][1], &R_sub_refl, &R_sub_fun, &R_sub_arg, &R_oblig, &R_oblig_lamty, &R_oblig_lam,
                     &R_just_nil, &R_just_cons, &R_just_hyp, &R_pin, &R_oblig_var,
                     &R_rocc_here, &R_rocc_arg, &R_rocc_fun, &R_rshape_cst, &R_rshape_pi, &R_rshape_sort[0],
                     &R_rshape_sort[1], &R_nosol, &R_nowf, &R_obchk_cst, &R_obchk_lam, &R_oblig_chk, &R_rocc_lam,
                     &R_rocc_lam_here, &R_nosol_bindv, &R_nosol_bindo, &R_nosol_up, &R_nosol_sort,
                     &R_epoch0, &R_head_var, &R_head_cst, &R_head_app, &R_hn_leaf[0], &R_hn_leaf[1], &R_hn_leaf[2],
                     &R_hn_pi, &R_hn_lam, &R_hn_var, &R_hn_static, &R_hn_def, &R_nmall_nil, &R_nmall_nm,
                     &R_nmall_short, &R_nm_lift, &R_lt0, &R_ltS, &R_wh, &R_nf, &R_nfw_var, &R_nfw_cst,
                     &R_nfw_leaf[0], &R_nfw_leaf[1], &R_nfw_leaf[2], &R_nfw_app, &R_nfw_lam, &R_nfw_pi,
                     &R_shape_leaf[0], &R_shape_leaf[1], &R_shape_leaf[2], &R_shape_pi, &R_shape_lam, &R_shape_var,
                     &R_shape_cst, &R_nc_shape, &R_nc_appf, &R_nc_appa, &R_nc_lam, &R_nc_pid, &R_nc_pic, &R_nc_etal,
                     &R_nc_etar, &R_notconv};
  size_t n = 0;
  for (size_t i = 0; i < sizeof mine / sizeof *mine; i++, n++)
    if (n < cap) out[n] = mine[i];
  return n + bl_rules(B, n < cap ? out + n : NULL, n < cap ? cap - n : 0);
}

/* --emit-tcs: every fixed rule as a schema of the specializer (theory "dk", rules r0, r1, ...). */
static int emit_tcs(const char *path) {
  size_t n = all_rules(NULL, 0);
  rk_rule **rs = xr(NULL, (n + 1) * sizeof *rs);
  all_rules(rs, n);
  tr_firing *fs = xr(NULL, (n + 1) * sizeof *fs);
  uint32_t *np = xr(NULL, (n + 1) * sizeof *np);
  const char **names = xr(NULL, (n + 1) * sizeof *names);
  char *buf = xr(NULL, (n + 1) * 16);
  for (size_t i = 0; i < n; i++) {
    rk_to_schema(C, rs[i], &fs[i], &np[i]);
    sprintf(buf + 16 * i, "r%zu", i);
    names[i] = buf + 16 * i;
  }
  char err[512];
  tcs_theory *t = tcs_theory_from_firings(C, "dk", n, names, fs, np, err, sizeof err);
  if (!t) {
    fprintf(stderr, "dk_ref: --emit-tcs: %s\n", err);
    return 2;
  }
  FILE *f = fopen(path, "w");
  bool ok = f && tcs_write(f, C, t, 1);
  if (f) fclose(f);
  tcs_free(t, 1);
  for (size_t i = 0; i < n; i++) rk_schema_free(&fs[i]);
  free(rs), free(fs), free(np), free(names), free(buf);
  if (!ok) fprintf(stderr, "dk_ref: --emit-tcs: cannot write %s\n", path);
  return ok ? 0 : 2;
}

#ifdef DK_SPEC
/* The specializer's code for the fixed rules (a file tcs_gen wrote from --emit-tcs): a rule takes
 * its compiled decision only when its compiled schema is, term for term, the rule as built in this
 * run (a profile or a planted fault that changes a rule keeps it on the generic route). */
static const tcs_compiled_theory *SPEC;
static tr_verdict spec_decide(int fast, tr_state *s, const tr_term *params, const tr_occ *occs, tr_result *r) {
  return SPEC->rules[fast].decide(s, params, occs, r, true);
}
static size_t spec_link(void) {
  for (size_t i = 0; i < tcs_ncompiled; i++)
    if (!strcmp(tcs_compiled[i].name, "dk")) SPEC = &tcs_compiled[i];
  if (!SPEC || !SPEC->link(C)) {
    fputs("dk_ref: the compiled rules cannot be linked\n", stderr);
    exit(2);
  }
  const tcs_theory *th = SPEC->schemas();
  size_t n = all_rules(NULL, 0), used = 0;
  rk_rule **rs = xr(NULL, (n + 1) * sizeof *rs);
  all_rules(rs, n);
  for (size_t i = 0; i < n && i < th->nrules; i++) {
    tr_firing f;
    uint32_t np;
    rk_to_schema(C, rs[i], &f, &np);
    const tcs_rule *t = &th->rules[i];
    bool same = t->nparams == np && t->fresh == f.fresh && t->ntakes == f.ntakes && t->nreads == f.nreads &&
                t->nmakes == f.nmakes && t->napart == f.napart && t->ntells == 0 && t->nguards == 0 && f.nguards == 0;
    for (size_t j = 0; same && j < f.ntakes; j++) same = t->takes[j] == f.takes[j].pattern;
    for (size_t j = 0; same && j < f.nreads; j++) same = t->reads[j] == f.reads[j].pattern;
    for (size_t j = 0; same && j < f.nmakes; j++) same = t->makes[j] == f.makes[j].label;
    for (size_t j = 0; same && j < f.napart; j++)
      same = t->apart[j].left == f.apart[j].left && t->apart[j].right == f.apart[j].right;
    rk_schema_free(&f);
    if (same && SPEC->rules[i].specialized) rs[i]->fast = (int)i, used++;
  }
  free(rs);
  E.decide = spec_decide;
  return used;
}
#endif

/* ============================================================================================
 * Firing, and the epoch.
 * ========================================================================================== */

static tr_occ fire(const rk_rule *r, const tr_occ *occs, const tr_term *vals) {
  return rk_fire(&E, r, occs, vals, NULL, NULL);
}
static tr_occ fire1(const rk_rule *r, tr_occ a, const tr_term *vals) { return fire(r, &a, vals); }
static tr_occ fire2(const rk_rule *r, tr_occ a, tr_occ b, const tr_term *vals) {
  tr_occ o[2] = {a, b};
  return fire(r, o, vals);
}
static tr_occ fire3(const rk_rule *r, tr_occ a, tr_occ b, tr_occ c, const tr_term *vals) {
  tr_occ o[3] = {a, b, c};
  return fire(r, o, vals);
}
static tr_term A_(tr_occ o, uint32_t i) { return rk_arg(&E, o, i); }

static tr_occ epoch_occ;
static tr_term epoch_name;
static uint32_t epoch_no; /* how many rule admissions so far: the C's stamp for memo entries */

/* ============================================================================================
 * Rewrite rules as compiled pattern trees and their firings.
 * ========================================================================================== */

enum { N_CST, N_BVAR, N_LAM, N_PVAR, N_BRK }; /* N_BRK: a bracket {t}, matched as a variable, then guarded */
typedef struct {
  int kind, parent;
  uint32_t depth, head, nargs; /* N_CST: head = symbol; N_BVAR: head = bound variable index */
  uint32_t pv, a, *ys;         /* N_PVAR */
  int first;                   /* N_PVAR: the node of the variable's first occurrence */
  int *kids;
  uint32_t lt, ldom, lred, lbody, linst; /* locals */
  tr_term rho;
  tr_term guard; /* N_BRK: the bracket's term, at the redex's scope (it mentions no pattern binder) */
} pnode;

typedef struct {
  uint32_t id, sym, k, m;
  pnode *nodes;
  uint32_t nnodes;
  int *top;
  int *first_of_pv;
  tr_term rhs, lhs, delta;
  uint32_t nlocals, lE, lW, lS, lN, lR;
  rk_rule match;
  rk_rule *clash;   /* per rigid node */
  rk_rule **miller; /* per pattern-variable node, per bound variable index (NULL: allowed) */
  rk_rule *nonlin;  /* per pattern-variable node that is not a first occurrence */
  const char *name;
} rrule;
static rrule *RR;
static uint32_t nrr, caprr;

static bool rigid(const pnode *n) { return n->kind != N_PVAR && n->kind != N_BRK; }

static tr_term shape_term(const rrule *R, const pnode *n) {
  if (n->kind == N_LAM) return LAM(L(n->ldom), L(R->nodes[n->kids[0]].lt));
  tr_term t = n->kind == N_CST ? CST(n->head) : VAR(n->head);
  for (uint32_t j = 0; j < n->nargs; j++) t = APP(t, L(R->nodes[n->kids[j]].lt));
  return t;
}
static tr_term pattern_shape(const pnode *n) {
  if (n->kind == N_LAM) return SL;
  if (n->kind == N_CST) return T2(f_sc, tr_code(C, n->head), NAT(n->nargs));
  return T2(f_sv, NAT(n->head), NAT(n->nargs));
}
static tr_term solution_term(const pnode *n) {
  tr_term s = L(n->lbody);
  for (uint32_t j = 0; j < n->a; j++) s = LAM(NONE, s);
  return s;
}
static tr_term lhs_top(const rrule *R) {
  tr_term t = CST(R->sym);
  for (uint32_t i = 0; i < R->k; i++) t = APP(t, L(R->nodes[R->top[i]].lt));
  return t;
}
/* The ancestors of node i, from the root down. */
static uint32_t ancestors(const rrule *R, int i, int *out) {
  uint32_t n = 0;
  for (int p = R->nodes[i].parent; p >= 0; p = R->nodes[p].parent) out[n++] = p;
  for (uint32_t a = 0, b = n; a + 1 < b; a++, b--) {
    int t = out[a];
    out[a] = out[b - 1];
    out[b - 1] = t;
  }
  return n;
}

static void read_ancestors_wh(rrule *R, rk_rule *r, const int *anc, uint32_t n) {
  for (uint32_t j = 0; j < n; j++) {
    const pnode *a = &R->nodes[anc[j]];
    rk_read(r, WH(L(a->lt), shape_term(R, a), L(R->lE)));
  }
}
static void failure_tail(rrule *R, rk_rule *r) {
  rk_make(r, T3(f_nomatch, tr_code(C, R->id), lhs_top(R), L(R->lE)));
  for (uint32_t i = 0; i < R->k; i++) rk_param(r, R->nodes[R->top[i]].lt);
}

static void install_firings(rrule *R) {
  /* locals: node targets first */
  uint32_t nl = R->nnodes;
  for (uint32_t i = 0; i < R->nnodes; i++) {
    pnode *n = &R->nodes[i];
    n->lt = i;
    if (n->kind == N_LAM) n->ldom = nl++;
    if (!rigid(n)) n->lred = nl++, n->lbody = nl++;
    if (n->kind == N_BRK) n->linst = nl++;
  }
  R->lR = nl++, R->lE = nl++, R->lW = nl++, R->lS = nl++, R->lN = nl++;
  R->nlocals = nl;
  /* the match firing */
  rk_init(&R->match, R->name, nl);
  for (uint32_t i = 0; i < R->nnodes; i++) {
    pnode *n = &R->nodes[i];
    if (rigid(n)) rk_read(&R->match, RD(L(n->lt), shape_term(R, n)));
    else {
      rk_read(&R->match, RD(L(n->lt), L(n->lred)));
      rk_read(&R->match, EV(L(n->lred), n->rho, L(n->lbody)));
      if (n->first != (int)i && FAULT != 3)
        rk_read(&R->match, CONV(solution_term(&R->nodes[n->first]), solution_term(n)));
    }
  }
  tr_term sigma = ID;
  for (uint32_t v = 0; v < R->m; v++) sigma = bl_cs(B, solution_term(&R->nodes[R->first_of_pv[v]]), sigma);
  rk_read(&R->match, EV(R->rhs, sigma, L(R->lR)));
  for (uint32_t i = 0; i < R->nnodes; i++) { /* each bracket's guard: its instance is convertible */
    pnode *n = &R->nodes[i];
    if (n->kind != N_BRK) continue;
    rk_read(&R->match, EV(n->guard, sigma, L(n->linst)));
    rk_read(&R->match, CONV(L(n->lbody), L(n->linst)));
  }
  rk_make(&R->match, RD(lhs_top(R), L(R->lR)));
  /* the failure firings */
  int *anc = xr(NULL, (R->nnodes + 1) * sizeof *anc), *anc2 = xr(NULL, (R->nnodes + 1) * sizeof *anc2);
  R->clash = xr(NULL, (R->nnodes + 1) * sizeof *R->clash);
  R->miller = xr(NULL, (R->nnodes + 1) * sizeof *R->miller);
  R->nonlin = xr(NULL, (R->nnodes + 1) * sizeof *R->nonlin);
  memset(R->clash, 0, (R->nnodes + 1) * sizeof *R->clash);
  memset(R->miller, 0, (R->nnodes + 1) * sizeof *R->miller);
  memset(R->nonlin, 0, (R->nnodes + 1) * sizeof *R->nonlin);
  for (uint32_t i = 0; i < R->nnodes; i++) {
    pnode *n = &R->nodes[i];
    uint32_t na = ancestors(R, (int)i, anc);
    if (rigid(n)) {
      rk_rule *r = &R->clash[i];
      rk_init(r, "a rule fails: a clash", nl);
      read_ancestors_wh(R, r, anc, na);
      rk_read(r, WH(L(n->lt), L(R->lW), L(R->lE)));
      rk_read(r, T2(f_shape, L(R->lW), L(R->lS)));
      rk_apart(r, L(R->lS), pattern_shape(n));
      failure_tail(R, r);
      continue;
    }
    R->miller[i] = xr(NULL, (n->depth + 1) * sizeof *R->miller[i]);
    for (uint32_t k = 0; k < n->depth; k++) {
      bool allowed = false;
      for (uint32_t j = 0; j < n->a; j++) allowed |= n->ys[j] == k;
      if (allowed) {
        R->miller[i][k].what = NULL;
        continue;
      }
      rk_rule *r = &R->miller[i][k];
      rk_init(r, "a rule fails: a forbidden bound variable", nl);
      read_ancestors_wh(R, r, anc, na);
      rk_read(r, T3(f_nf, L(n->lt), L(R->lN), L(R->lE)));
      rk_read(r, bl_mentions_fact(B, L(R->lN), NAT(k)));
      failure_tail(R, r);
    }
    if (n->first != (int)i) {
      pnode *f = &R->nodes[n->first];
      uint32_t nb = ancestors(R, n->first, anc2);
      /* the union of the two ancestor chains, in node order */
      bool *in = xr(NULL, R->nnodes + 1);
      memset(in, 0, R->nnodes + 1);
      for (uint32_t j = 0; j < na; j++) in[anc[j]] = true;
      for (uint32_t j = 0; j < nb; j++) in[anc2[j]] = true;
      uint32_t nu = 0;
      for (uint32_t j = 0; j < R->nnodes; j++)
        if (in[j]) anc[nu++] = (int)j;
      free(in);
      rk_rule *r = &R->nonlin[i];
      rk_init(r, "a rule fails: repeated variable, instances not convertible", nl);
      read_ancestors_wh(R, r, anc, nu);
      rk_read(r, RD(L(f->lt), L(f->lred)));
      rk_read(r, EV(L(f->lred), f->rho, L(f->lbody)));
      rk_read(r, RD(L(n->lt), L(n->lred)));
      rk_read(r, EV(L(n->lred), n->rho, L(n->lbody)));
      rk_read(r, T3(f_notconv, solution_term(f), solution_term(n), L(R->lE)));
      failure_tail(R, r);
    }
  }
  free(anc);
  free(anc2);
}

/* ============================================================================================
 * The work order: reduction, conversion (positive).
 * ========================================================================================== */

static map M_refl, M_whnf, M_snf, M_conv, M_ty, M_ctx, M_lookup, M_head, M_shape, M_hn, M_wh, M_nf, M_nfw,
    M_notconv, M_lt;

static tr_occ rd_refl(tr_term t) {
  ment *e = map_find(&M_refl, t + 1);
  if (e) return e->occ;
  tr_occ o = fire(&R_rd_refl, NULL, &t);
  map_put(&M_refl, t + 1)->occ = o;
  return o;
}
static tr_occ rd_trans(tr_occ a, tr_occ b) {
  if (A_(a, 0) == A_(a, 1)) return b;
  if (A_(b, 0) == A_(b, 1)) return a;
  return fire2(&R_rd_trans, a, b, NULL);
}
/* From rd(p, p'), rd(p a1 .. an, p' a1 .. an) for the arguments args[0..n-1] (outermost last). */
static tr_occ rd_under(tr_occ o, const tr_term *args, uint32_t n) {
  for (uint32_t i = 0; i < n; i++) o = fire2(&R_rd_app, o, rd_refl(args[i]), NULL);
  return o;
}

static tr_occ whnf_pos(tr_term t, tr_term *w);
static tr_occ snf_pos(tr_term t, tr_term *n);
static tr_occ conv_pos(tr_term a, tr_term b);
static tr_occ match_pos(rrule *R, tr_term P);
static tr_occ notconv_neg(tr_term a, tr_term b);

/* One head step of cur (a spine): its occurrence rd(cur, next), or 0 when cur is weak head normal. */
static tr_occ head_step(tr_term cur, tr_term *next) {
  uint32_t n;
  tr_term h = spine(cur, &n);
  tr_term small[16], *args = n <= 16 ? small : xr(NULL, n * sizeof *args);
  { /* the arguments, outermost last */
    tr_term t = cur;
    for (uint32_t i = n; i-- > 0;) args[i] = arg(t, 1), t = arg(t, 0);
  }
  tr_occ out = 0;
  uint32_t k;
  if (is_lam(h) && n >= 1) {
    tr_term r;
    tr_occ oe = bl_ev(B, arg(h, 1), bl_cs(B, args[0], ID), &r);
    if (!oe) noverdict("internal: a beta step has no substitution fact");
    tr_term d = arg(h, 0);
    tr_occ o = fire1(&R_rd_beta, oe, &d);
    out = rd_under(o, args + 1, n - 1);
  } else if (is_cst(h, &k) && SY[k].kind == SK_DEFN) {
    tr_occ o = fire1(&R_rd_delta, SY[k].defn, NULL);
    out = rd_under(o, args, n);
  } else if (is_cst(h, &k) && SY[k].kind == SK_DEFINABLE) {
    for (size_t j = 0; j < SY[k].nrl && !out; j++) {
      rrule *R = &RR[SY[k].rl[j]];
      if (R->k > n) continue;
      tr_occ o = match_pos(R, strip(cur, n - R->k));
      if (o) out = rd_under(o, args + R->k, n - R->k);
    }
  }
  if (args != small) free(args);
  if (out) *next = A_(out, 1);
  return out;
}

static uint64_t steps;
static tr_occ whnf_pos(tr_term t, tr_term *w) {
  deep();
  ment *e = map_find(&M_whnf, t + 1);
  tr_occ o;
  tr_term cur;
  if (e) {
    o = e->occ, cur = e->val;
    if (e->stamp == epoch_no) {
      *w = cur;
      return o;
    }
  } else
    o = rd_refl(t), cur = t;
  for (;;) {
    tr_term next;
    tr_occ s = head_step(cur, &next);
    if (!s) break;
    if (++steps % 1000000 == 0 && !QUIET) fprintf(stderr, "dk_ref: %llu head steps\n", (unsigned long long)steps);
    o = rd_trans(o, s);
    cur = next;
  }
  e = map_put(&M_whnf, t + 1);
  e->occ = o, e->val = cur, e->stamp = epoch_no;
  *w = cur;
  return o;
}

/* Strong normalization (positive): rd(t, n). */
static tr_occ snf_pos(tr_term t, tr_term *n) {
  deep();
  ment *e = map_find(&M_snf, t + 1);
  if (e && e->stamp == epoch_no) {
    *n = e->val;
    return e->occ;
  }
  tr_term w;
  tr_occ o = whnf_pos(t, &w), inner = 0;
  if (is_app(w) || is_lam(w) || is_pi(w)) {
    tr_term a, b;
    tr_occ oa = snf_pos(arg(w, 0), &a), ob = snf_pos(arg(w, 1), &b);
    inner = fire2(is_app(w) ? &R_rd_app : is_lam(w) ? &R_rd_lam : &R_rd_pi, oa, ob, NULL);
  }
  if (inner) o = rd_trans(o, inner);
  e = map_put(&M_snf, t + 1);
  e->occ = o, e->val = A_(o, 1), e->stamp = epoch_no;
  *n = e->val;
  return o;
}

/* conv(w1, w2) for weak head normal forms, or 0. */
static tr_occ conv_whnf(tr_term a, tr_term b) {
  if (a == b) return fire(&R_cv_refl, NULL, &a);
  if (is_app(a) && is_app(b)) {
    uint32_t na, nb;
    spine(a, &na), spine(b, &nb);
    if (na != nb) return 0;
    tr_occ o1 = conv_pos(arg(a, 0), arg(b, 0));
    if (!o1) return 0;
    tr_occ o2 = conv_pos(arg(a, 1), arg(b, 1));
    return o2 ? fire2(&R_cv_app, o1, o2, NULL) : 0;
  }
  if (is_lam(a) && is_lam(b)) {
    tr_occ o = conv_pos(arg(a, 1), arg(b, 1));
    tr_term v[2] = {arg(a, 0), arg(b, 0)};
    return o ? fire1(&R_cv_lam, o, v) : 0;
  }
  if (is_pi(a) && is_pi(b)) {
    if (FAULT == 4) {
      tr_occ o2 = conv_pos(arg(a, 1), arg(b, 1));
      tr_term v[2] = {arg(a, 0), arg(b, 0)};
      return o2 ? fire1(&R_cv_pi, o2, v) : 0;
    }
    tr_occ o1 = conv_pos(arg(a, 0), arg(b, 0));
    if (!o1) return 0;
    tr_occ o2 = conv_pos(arg(a, 1), arg(b, 1));
    return o2 ? fire2(&R_cv_pi, o1, o2, NULL) : 0;
  }
  if (ETA && (is_lam(a) || is_lam(b))) {
    bool left = is_lam(a);
    tr_term lam = left ? a : b, other = left ? b : a, sh;
    tr_occ oe = bl_ev(B, other, SH, &sh);
    if (!oe) return 0;
    tr_term ex = APP(sh, VAR(0));
    tr_occ oc = left ? conv_pos(arg(lam, 1), ex) : conv_pos(ex, arg(lam, 1));
    tr_term d = arg(lam, 0);
    return oc ? fire2(left ? &R_cv_etal : &R_cv_etar, oe, oc, &d) : 0;
  }
  return 0;
}

static tr_occ conv_pos(tr_term a, tr_term b) {
  deep();
  if (a == b) return fire(&R_cv_refl, NULL, &a);
  ment *e = map_find(&M_conv, K2(a, b));
  if (e && (e->occ || e->stamp == epoch_no)) return e->occ;
  tr_term wa, wb;
  tr_occ oa = whnf_pos(a, &wa), ob = whnf_pos(b, &wb);
  tr_occ o = conv_whnf(wa, wb);
  if (o && wb != b) o = fire2(&R_cv_redr, ob, o, NULL);
  if (o && wa != a) o = fire2(&R_cv_redl, oa, o, NULL);
  e = map_put(&M_conv, K2(a, b));
  e->occ = o, e->stamp = epoch_no;
  return o;
}

/* ============================================================================================
 * Matching (positive): the facts the rule's match firing reads, in its order.
 * ========================================================================================== */

static tr_occ *mocc;
static size_t nmocc, capmocc;
static void mpush(tr_occ o) {
  GROW(mocc, nmocc, capmocc);
  mocc[nmocc++] = o;
}

/* The children's targets of a rigid node whose target's weak head normal form w has its shape. */
static bool shape_matches(const pnode *n, tr_term w) {
  if (n->kind == N_LAM) return is_lam(w);
  uint32_t k, m;
  tr_term h = spine(w, &m);
  if (m != n->nargs) return false;
  if (n->kind == N_CST) return is_cst(h, &k) && k == n->head;
  return is_var(h, &k) && k == n->head;
}
static void set_kids(rrule *R, const pnode *n, tr_term w, tr_term *tg) {
  if (n->kind == N_LAM) {
    tg[n->kids[0]] = arg(w, 1);
    return;
  }
  for (uint32_t j = 0; j < n->nargs; j++) tg[n->kids[j]] = spine_arg(w, n->nargs, j);
  (void)R;
}
static tr_term lams(uint32_t a, tr_term body) {
  while (a--) body = LAM(NONE, body);
  return body;
}

static tr_occ match_pos(rrule *R, tr_term P) {
  deep();
  tr_term *tg = xr(NULL, (R->nnodes + 1) * sizeof *tg), *sol = xr(NULL, (R->nnodes + 1) * sizeof *sol);
  for (uint32_t i = 0; i < R->k; i++) tg[R->top[i]] = spine_arg(P, R->k, i);
  size_t base = nmocc;
  tr_occ out = 0;
  bool ok = true;
  for (uint32_t i = 0; ok && i < R->nnodes; i++) {
    pnode *n = &R->nodes[i];
    if (rigid(n)) {
      tr_term w;
      tr_occ o = whnf_pos(tg[i], &w);
      if (!shape_matches(n, w)) ok = false;
      else mpush(o), set_kids(R, n, w, tg);
      continue;
    }
    tr_term t2 = tg[i], body;
    tr_term rho = n->rho;
    if (LIE == 3) { /* lie 3: the renaming without the depth - arity transport (Dedukti's `else n`) */
      int saved = bl_fault;
      bl_fault = 5;
      rho = bl_rho(B, n->depth, n->ys, n->a);
      bl_fault = saved;
    }
    tr_occ o1 = rd_refl(t2), o2 = bl_ev(B, t2, rho, &body);
    if (!o2) { /* Dedukti's force_solve: the instance in normal form */
      o1 = snf_pos(tg[i], &t2);
      o2 = bl_ev(B, t2, rho, &body);
    }
    if (!o2) {
      ok = false;
      continue;
    }
    mpush(o1), mpush(o2);
    sol[i] = lams(n->a, body);
    if (n->first != (int)i && FAULT != 3) {
      tr_occ oc = LIE == 2 ? fire(&R_cv_refl, NULL, &sol[i]) : conv_pos(sol[n->first], sol[i]);
      if (!oc) ok = false;
      else mpush(oc);
    }
  }
  if (ok) {
    tr_term sigma = ID, r;
    for (uint32_t v = 0; v < R->m; v++) sigma = bl_cs(B, sol[R->first_of_pv[v]], sigma);
    tr_occ o = bl_ev(B, R->rhs, sigma, &r);
    if (!o) noverdict("internal: the right-hand side of %s has no instance", R->name);
    mpush(o);
    for (uint32_t i = 0; i < R->nnodes; i++) { /* the brackets' guards */
      pnode *n = &R->nodes[i];
      if (n->kind != N_BRK) continue;
      tr_term inst;
      tr_occ oe = bl_ev(B, n->guard, sigma, &inst);
      if (!oe) noverdict("internal: a bracket of %s has no instance", R->name);
      tr_occ oc = conv_pos(sol[i], inst);
      if (!oc) { /* Dedukti: a guard that is not satisfied is an error, not a failed match */
        tr_occ on = notconv_neg(sol[i], inst);
        if (on) refuse(BY_FACT, "a bracket's guard is not satisfied in %s (notconv fact %llu)", R->name, (unsigned long long)on);
        refuse(BY_ORDER, "a bracket's guard is not satisfied in %s", R->name);
      }
      mpush(oe), mpush(oc);
    }
    out = fire(&R->match, mocc + base, NULL);
    if (!out && !LIE) noverdict("internal: the match firing of %s was refused", R->name);
    if (!out) fprintf(stderr, "dk_ref: the step refused the match firing of %s (a lie)\n", R->name);
  }
  nmocc = base;
  free(tg);
  free(sol);
  return out;
}

/* ============================================================================================
 * The work order: negative judgments.
 * ========================================================================================== */

static tr_occ head_of(tr_term w) {
  ment *e = map_find(&M_head, w + 1);
  if (e) return e->occ;
  tr_occ o = 0;
  uint32_t k;
  if (is_var(w, &k)) {
    tr_term n = arg(w, 0);
    o = fire(&R_head_var, NULL, &n);
  } else if (is_cst(w, &k)) {
    tr_term c = arg(w, 0);
    o = fire(&R_head_cst, NULL, &c);
  } else if (is_app(w)) {
    tr_occ oh = head_of(arg(w, 0));
    tr_term b = arg(w, 1);
    if (oh) o = fire1(&R_head_app, oh, &b);
  }
  map_put(&M_head, w + 1)->occ = o;
  return o;
}

static tr_occ shape_of(tr_term w) {
  ment *e = map_find(&M_shape, w + 1);
  if (e) return e->occ;
  tr_occ o = 0;
  if (w == TYPE) o = fire(&R_shape_leaf[0], NULL, NULL);
  else if (w == KIND) o = fire(&R_shape_leaf[1], NULL, NULL);
  else if (w == NONE) o = fire(&R_shape_leaf[2], NULL, NULL);
  else if (is_pi(w) || is_lam(w)) {
    tr_term v[2] = {arg(w, 0), arg(w, 1)};
    o = fire(is_pi(w) ? &R_shape_pi : &R_shape_lam, NULL, v);
  } else {
    uint32_t n, k;
    tr_term h = spine(w, &n);
    tr_occ oh = head_of(w);
    if (oh) o = fire1(is_var(h, &k) ? &R_shape_var : &R_shape_cst, oh, NULL);
  }
  map_put(&M_shape, w + 1)->occ = o;
  return o;
}

static tr_occ lt_of(uint32_t n, uint32_t k) {
  ment *e = map_find(&M_lt, K2(n, k));
  if (e) return e->occ;
  tr_occ o;
  if (n == 0) {
    tr_term km = NAT(k - 1);
    o = fire(&R_lt0, NULL, &km);
  } else
    o = fire1(&R_ltS, lt_of(n - 1, k - 1), NULL);
  map_put(&M_lt, K2(n, k))->occ = o;
  return o;
}

static tr_occ wh_neg(tr_term t, tr_term *w);
static tr_occ nf_neg(tr_term t, tr_term *n);
static tr_occ notconv_neg(tr_term a, tr_term b);
static tr_occ nomatch_exact(rrule *R, tr_term P);

/* nomatch(R, w, E), w with n >= R->k arguments. */
static tr_occ nomatch_neg(rrule *R, tr_term w, uint32_t n) {
  tr_occ o = nomatch_exact(R, strip(w, n - R->k));
  if (!o) return 0;
  for (uint32_t i = R->k; i < n; i++) { /* lift through the arguments, innermost first */
    tr_term b = spine_arg(w, n, i);
    o = fire1(&R_nm_lift, o, &b);
  }
  return o;
}

/* hn(w, E) for a weak head normal form w (at the current epoch). */
static tr_occ hn_neg(tr_term w) {
  ment *e = map_find(&M_hn, w + 1);
  if (e && e->stamp == epoch_no) return e->occ;
  tr_occ o = 0;
  uint32_t k, n;
  if (w == TYPE) o = fire1(&R_hn_leaf[0], epoch_occ, NULL);
  else if (w == KIND) o = fire1(&R_hn_leaf[1], epoch_occ, NULL);
  else if (w == NONE) o = fire1(&R_hn_leaf[2], epoch_occ, NULL);
  else if (is_pi(w) || is_lam(w)) {
    tr_term v[2] = {arg(w, 0), arg(w, 1)};
    o = fire1(is_pi(w) ? &R_hn_pi : &R_hn_lam, epoch_occ, v);
  } else {
    tr_term h = spine(w, &n);
    tr_occ oh = head_of(w);
    if (oh && is_var(h, &k)) o = fire2(&R_hn_var, oh, epoch_occ, NULL);
    else if (oh && is_cst(h, &k) && (SY[k].kind == SK_STATIC || SY[k].kind == SK_THM)) {
      tr_occ os[3] = {oh, SY[k].stat, epoch_occ};
      o = fire(&R_hn_static, os, NULL);
    } else if (oh && is_cst(h, &k) && SY[k].kind == SK_DEFINABLE) {
      /* the rule list as the rules fact holds it, oldest first */
      tr_term list = A_(SY[k].rules, 1);
      size_t cnt = 0;
      for (tr_term l = list; l != NIL; l = arg(l, 1)) cnt++;
      tr_term *items = xr(NULL, (cnt + 1) * sizeof *items);
      size_t i = cnt;
      for (tr_term l = list; l != NIL; l = arg(l, 1)) items[--i] = arg(l, 0);
      tr_term v[2] = {w, NAT(n)};
      tr_occ acc = fire1(&R_nmall_nil, epoch_occ, v);
      for (i = 0; acc && i < cnt; i++) {
        uint32_t rid = (uint32_t)tr_term_code(C, arg(items[i], 0)), kar;
        if (!bl_nat_value(B, arg(items[i], 1), &kar)) noverdict("internal: a rule arity");
        if (n < kar) {
          tr_term rr = arg(items[i], 0);
          acc = fire2(&R_nmall_short, acc, lt_of(n, kar), &rr);
        } else {
          tr_occ onm = nomatch_neg(&RR[rid], w, n);
          tr_term kk = arg(items[i], 1);
          acc = onm ? fire2(&R_nmall_nm, acc, onm, &kk) : 0;
        }
      }
      free(items);
      if (acc) o = fire3(&R_hn_def, oh, SY[k].rules, acc, NULL);
    }
  }
  e = map_put(&M_hn, w + 1);
  e->occ = o, e->stamp = epoch_no;
  return o;
}

static tr_occ wh_neg(tr_term t, tr_term *w) {
  deep();
  ment *e = map_find(&M_wh, t + 1);
  if (e && e->stamp == epoch_no) {
    *w = e->val;
    return e->occ;
  }
  tr_occ o1 = whnf_pos(t, w), o2 = hn_neg(*w), o = o2 ? fire2(&R_wh, o1, o2, NULL) : 0;
  e = map_put(&M_wh, t + 1);
  e->occ = o, e->val = *w, e->stamp = epoch_no;
  return o;
}

static tr_occ nfw_neg(tr_term w) {
  deep();
  ment *e = map_find(&M_nfw, w + 1);
  if (e && e->stamp == epoch_no) return e->occ;
  tr_occ o = 0;
  uint32_t k;
  tr_term x;
  if (w == TYPE) o = fire1(&R_nfw_leaf[0], epoch_occ, NULL);
  else if (w == KIND) o = fire1(&R_nfw_leaf[1], epoch_occ, NULL);
  else if (w == NONE) o = fire1(&R_nfw_leaf[2], epoch_occ, NULL);
  else if (is_var(w, &k)) {
    x = arg(w, 0);
    o = fire1(&R_nfw_var, epoch_occ, &x);
  } else if (is_cst(w, &k)) {
    x = arg(w, 0);
    o = fire1(&R_nfw_cst, epoch_occ, &x);
  } else if (is_app(w)) {
    tr_term n;
    tr_occ oa = nfw_neg(arg(w, 0)), ob = oa ? nf_neg(arg(w, 1), &n) : 0;
    if (ob) o = fire2(&R_nfw_app, oa, ob, NULL);
  } else if (is_lam(w) || is_pi(w)) {
    tr_term n;
    tr_occ oa = nf_neg(arg(w, 0), &n), ob = oa ? nf_neg(arg(w, 1), &n) : 0;
    if (ob) o = fire2(is_lam(w) ? &R_nfw_lam : &R_nfw_pi, oa, ob, NULL);
  }
  e = map_put(&M_nfw, w + 1);
  e->occ = o, e->stamp = epoch_no;
  return o;
}

static tr_occ nf_neg(tr_term t, tr_term *n) {
  deep();
  ment *e = map_find(&M_nf, t + 1);
  if (e && e->stamp == epoch_no) {
    *n = e->val;
    return e->occ;
  }
  tr_term w;
  tr_occ o1 = wh_neg(t, &w), o2 = o1 ? nfw_neg(w) : 0, o = o2 ? fire2(&R_nf, o1, o2, NULL) : 0;
  e = map_put(&M_nf, t + 1);
  e->occ = o, e->val = o ? A_(o, 1) : TR_NONE, e->stamp = epoch_no;
  *n = e->val;
  return o;
}

/* nc(w1, w2, E) for weak head normal forms. */
static tr_occ nc_neg(tr_term a, tr_term b) {
  deep();
  tr_occ sa = shape_of(a), sb = shape_of(b);
  if (!sa || !sb) return 0;
  tr_term ha = A_(sa, 1), hb = A_(sb, 1);
  if (ha != hb && !(ETA && (ha == SL || hb == SL))) {
    tr_occ o[3] = {sa, sb, epoch_occ};
    return fire(&R_nc_shape, o, NULL);
  }
  if (ha != hb) { /* eta: an abstraction against something else */
    bool left = ha == SL;
    tr_term lam = left ? a : b, other = left ? b : a, sh;
    tr_occ oe = bl_ev(B, other, SH, &sh);
    tr_term ex = APP(sh, VAR(0));
    tr_occ on = left ? notconv_neg(arg(lam, 1), ex) : notconv_neg(ex, arg(lam, 1));
    if (!oe || !on) return 0;
    tr_term d = arg(lam, 0);
    return fire3(left ? &R_nc_etal : &R_nc_etar, left ? sb : sa, oe, on, &d);
  }
  if (is_lam(a)) {
    tr_occ on = notconv_neg(arg(a, 1), arg(b, 1));
    tr_term v[2] = {arg(a, 0), arg(b, 0)};
    return on ? fire1(&R_nc_lam, on, v) : 0;
  }
  if (is_pi(a)) {
    if (!conv_pos(arg(a, 0), arg(b, 0))) {
      tr_occ on = notconv_neg(arg(a, 0), arg(b, 0));
      tr_term v[2] = {arg(a, 1), arg(b, 1)};
      return on ? fire1(&R_nc_pid, on, v) : 0;
    }
    tr_occ on = notconv_neg(arg(a, 1), arg(b, 1));
    tr_term v[2] = {arg(a, 0), arg(b, 0)};
    return on ? fire1(&R_nc_pic, on, v) : 0;
  }
  if (is_app(a) && is_app(b)) {
    if (!conv_pos(arg(a, 1), arg(b, 1))) {
      tr_occ on = notconv_neg(arg(a, 1), arg(b, 1));
      tr_term v[2] = {arg(a, 0), arg(b, 0)};
      return on ? fire1(&R_nc_appa, on, v) : 0;
    }
    tr_occ on = nc_neg(arg(a, 0), arg(b, 0));
    tr_term v[2] = {arg(a, 1), arg(b, 1)};
    return on ? fire1(&R_nc_appf, on, v) : 0;
  }
  return 0;
}

static tr_occ notconv_neg(tr_term a, tr_term b) {
  deep();
  ment *e = map_find(&M_notconv, K2(a, b));
  if (e && e->stamp == epoch_no) return e->occ;
  tr_term wa, wb;
  tr_occ oa = wh_neg(a, &wa), ob = oa ? wh_neg(b, &wb) : 0, onc = ob ? nc_neg(wa, wb) : 0;
  tr_occ o = onc ? fire3(&R_notconv, oa, ob, onc, NULL) : 0;
  e = map_put(&M_notconv, K2(a, b));
  e->occ = o, e->stamp = epoch_no;
  return o;
}

/* nomatch(R, P, E): the failure the rule meets on P (exactly R->k arguments). */
static tr_occ nomatch_exact(rrule *R, tr_term P) {
  deep();
  tr_term *tg = xr(NULL, (R->nnodes + 1) * sizeof *tg), *sol = xr(NULL, (R->nnodes + 1) * sizeof *sol);
  tr_occ *wocc = xr(NULL, (R->nnodes + 1) * sizeof *wocc), *mo1 = xr(NULL, (R->nnodes + 1) * sizeof *mo1),
         *mo2 = xr(NULL, (R->nnodes + 1) * sizeof *mo2);
  int *anc = xr(NULL, (R->nnodes + 1) * sizeof *anc);
  for (uint32_t i = 0; i < R->k; i++) tg[R->top[i]] = spine_arg(P, R->k, i);
  tr_term *tops = xr(NULL, (R->k + 1) * sizeof *tops);
  for (uint32_t i = 0; i < R->k; i++) tops[i] = tg[R->top[i]];
  size_t base = nmocc;
  tr_occ out = 0;
  bool done = false;
  for (uint32_t i = 0; !done && i < R->nnodes; i++) {
    pnode *n = &R->nodes[i];
    uint32_t na = ancestors(R, (int)i, anc);
    if (rigid(n)) {
      tr_term w;
      tr_occ o = wh_neg(tg[i], &w);
      if (!o) {
        done = true;
        break;
      }
      if (!shape_matches(n, w)) {
        tr_occ os = shape_of(w);
        nmocc = base;
        for (uint32_t j = 0; j < na; j++) mpush(wocc[anc[j]]);
        mpush(o), mpush(os);
        out = os ? fire(&R->clash[i], mocc + base, tops) : 0;
        done = true;
        break;
      }
      wocc[i] = o;
      set_kids(R, n, w, tg);
      continue;
    }
    tr_term t2 = tg[i], body;
    tr_occ o1 = rd_refl(t2), o2 = bl_ev(B, t2, n->rho, &body);
    if (!o2) {
      o1 = snf_pos(tg[i], &t2);
      o2 = bl_ev(B, t2, n->rho, &body);
    }
    if (!o2) { /* a forbidden bound variable occurs in the instance's normal form */
      tr_term nform;
      tr_occ onf = nf_neg(tg[i], &nform);
      for (uint32_t k = 0; onf && k < n->depth && !out; k++) {
        if (!R->miller[i][k].what) continue;
        tr_occ om = bl_mentions(B, nform, k);
        if (!om) continue;
        nmocc = base;
        for (uint32_t j = 0; j < na; j++) mpush(wocc[anc[j]]);
        mpush(onf), mpush(om);
        out = fire(&R->miller[i][k], mocc + base, tops);
      }
      done = true;
      break;
    }
    mo1[i] = o1, mo2[i] = o2;
    sol[i] = lams(n->a, body);
    if (n->first != (int)i && !conv_pos(sol[n->first], sol[i])) {
      tr_occ onc = notconv_neg(sol[n->first], sol[i]);
      if (onc) {
        int *anc2 = xr(NULL, (R->nnodes + 1) * sizeof *anc2);
        uint32_t nb = ancestors(R, n->first, anc2);
        bool *in = xr(NULL, R->nnodes + 1);
        memset(in, 0, R->nnodes + 1);
        for (uint32_t j = 0; j < na; j++) in[anc[j]] = true;
        for (uint32_t j = 0; j < nb; j++) in[anc2[j]] = true;
        nmocc = base;
        for (uint32_t j = 0; j < R->nnodes; j++)
          if (in[j]) mpush(wocc[j]);
        mpush(mo1[n->first]), mpush(mo2[n->first]), mpush(o1), mpush(o2), mpush(onc);
        out = fire(&R->nonlin[i], mocc + base, tops);
        free(in);
        free(anc2);
      }
      done = true;
      break;
    }
  }
  nmocc = base;
  free(tg), free(sol), free(wocc), free(mo1), free(mo2), free(anc), free(tops);
  return out; /* 0: the rule matches, or no failure could be derived */
}

/* ============================================================================================
 * The work order: typing.
 * ========================================================================================== */

static tr_occ ctx_of(tr_term g);
static tr_occ infer(tr_term g, tr_term t, tr_term *ty);
static tr_occ check(tr_term g, tr_term t, tr_term want, tr_occ *conv);

/* ---- conversion relative to a context's hypotheses ---- */

static void fv_mark(tr_term t, uint32_t depth, uint8_t *mark, uint32_t m);

static bool is_hyp(tr_term g) { return head_sym(g) == f_hyp; }
static bool has_hyp(tr_term g) {
  for (; g != NIL; g = is_hyp(g) ? arg(g, 2) : arg(g, 1))
    if (is_hyp(g)) return true;
  return false;
}
static tr_occ cv_sym(tr_occ o) { return fire1(&R_cv_sym, o, NULL); }
static tr_occ cv_trans(tr_occ a, tr_occ b) {
  if (A_(a, 1) == A_(a, 2)) return b;
  if (A_(b, 1) == A_(b, 2)) return a;
  return fire2(&R_cv_trans, a, b, NULL);
}
static tr_occ cv_conv(tr_term g, tr_occ conv) { return fire1(&R_cv_conv, conv, &g); }
static tr_occ cv_refl(tr_term g, tr_term x) { return cv_conv(g, fire(&R_cv_refl, NULL, &x)); }
/* cv(g, a, a') from rd(a, a') */
static tr_occ cv_of_rd(tr_term g, tr_occ rd) {
  tr_term a2 = A_(rd, 1);
  tr_occ o = cv_refl(g, a2);
  return A_(rd, 0) == a2 ? o : fire2(&R_cv_red, rd, o, NULL);
}

typedef struct {
  tr_term a, b;
  tr_occ o; /* cv(g, a, b) */
} hpair;
typedef struct {
  hpair *v;
  size_t n, cap;
} hlist;
static void hpush(hlist *l, tr_term a, tr_term b, tr_occ o) {
  GROW(l->v, l->n, l->cap);
  l->v[l->n++] = (hpair){a, b, o};
}

static void hlist_under(tr_term g, tr_term d, const hlist *in, hlist *out);

/* Every hypothesis of g, as a fact cv(g, a, b) at g's own scope. */
static void hyps_in(tr_term g, hlist *out) {
  if (g == NIL) return;
  hlist inner = {0};
  if (is_hyp(g)) {
    tr_term v[3] = {arg(g, 0), arg(g, 1), arg(g, 2)};
    hpush(out, v[0], v[1], fire(&R_cv_hyp, NULL, v));
    hyps_in(v[2], &inner);
    for (size_t i = 0; i < inner.n; i++) hpush(out, inner.v[i].a, inner.v[i].b, fire1(&R_cv_wk_hyp, inner.v[i].o, v));
  } else {
    hyps_in(arg(g, 1), &inner);
    hlist_under(arg(g, 1), arg(g, 0), &inner, out);
  }
  free(inner.v);
}

/* Spines h a_1 .. a_n with h static, n >= 1: decompose a == b into the arguments' equations. */
static void decompose(tr_term g, tr_term a, tr_term b, tr_occ o, hlist *out) {
  uint32_t na, nb, k1, k2;
  tr_term ha = spine(a, &na), hb = spine(b, &nb);
  if (na && na == nb && is_cst(ha, &k1) && is_cst(hb, &k2) && k1 == k2 && (SY[k1].stat || SY[k1].inj)) {
    tr_occ hf = head_of(arg(a, 0)), hg = head_of(arg(b, 0));
    int inj = !SY[k1].stat;
    tr_occ os[4] = {o, hf, hg, inj ? SY[k1].inj : SY[k1].stat};
    tr_occ oarg = fire(&R_cv_dec[inj][0], os, NULL), ofun = fire(&R_cv_dec[inj][1], os, NULL);
    if (oarg && ofun) {
      hpush(out, arg(a, 1), arg(b, 1), oarg);
      decompose(g, arg(a, 0), arg(b, 0), ofun, out);
      return;
    }
  }
  if (a != b) hpush(out, a, b, o);
}

static void decompose(tr_term g, tr_term a, tr_term b, tr_occ o, hlist *out);

/* The equations of a list (in context g), moved under one binder of domain d; an equation
 * between abstractions also gives the one between their bodies at the new variable (both sides
 * applied to it, then beta), decomposed at static heads. */
static void hlist_under(tr_term g, tr_term d, const hlist *in, hlist *out) {
  tr_term g2 = CONS(d, g), v0 = VAR(0);
  for (size_t i = 0; i < in->n; i++) {
    tr_term a2, b2;
    tr_occ oa = bl_ev(B, in->v[i].a, SH, &a2), ob = bl_ev(B, in->v[i].b, SH, &b2);
    tr_occ o = fire3(&R_cv_wk_cons, in->v[i].o, oa, ob, &d);
    hpush(out, a2, b2, o);
    if (!is_lam(a2) || !is_lam(b2)) continue;
    tr_term xa = APP(a2, v0), xb = APP(b2, v0), na, nb;
    tr_occ oapp = fire2(&R_cvh_app, o, cv_refl(g2, v0), NULL); /* cv(g2, a2 v0, b2 v0) */
    tr_occ ra = snf_pos(xa, &na), rb = snf_pos(xb, &nb);
    tr_occ c = cv_trans(cv_sym(cv_of_rd(g2, ra)), cv_trans(oapp, cv_of_rd(g2, rb))); /* cv(g2, na, nb) */
    decompose(g2, na, nb, c, out);
  }
}

/* x with every variable bound by `bind` replaced, and cv(g, x, x'). */
static tr_occ subst_cv(tr_term g, tr_term x, const hlist *bind, tr_term *x2) {
  deep();
  uint32_t k;
  if (bl_free_bound(B, x) == 0 || !bind->n) {
    /* closed: nothing to replace */
  } else if (is_var(x, &k)) {
    for (size_t i = 0; i < bind->n; i++)
      if (bind->v[i].a == x) {
        *x2 = bind->v[i].b;
        return bind->v[i].o;
      }
  } else if (is_app(x) && is_var(arg(x, 0), &k)) {
    /* an applied variable with a higher-order solution x => t (the pair (x => X x, x => t)): both
     * applied to the argument u and reduced, X u == t[u/] (no eta is needed) */
    tr_term f = arg(x, 0), u = arg(x, 1), pat = APP(VAR(k + 1), VAR(0));
    for (size_t i = 0; i < bind->n; i++) {
      tr_term a = bind->v[i].a, b = bind->v[i].b;
      if (!is_lam(a) || arg(a, 1) != pat || !is_lam(b)) continue;
      tr_occ oc = fire2(&R_cvh_app, bind->v[i].o, cv_refl(g, u), NULL); /* cv(g, a u, b u) */
      tr_term r1, r2;
      tr_occ rd1 = whnf_pos(APP(a, u), &r1), rd2 = whnf_pos(APP(b, u), &r2);
      if (r1 != x) continue;
      *x2 = r2;
      return cv_trans(cv_sym(cv_of_rd(g, rd1)), cv_trans(oc, cv_of_rd(g, rd2)));
    }
    tr_term f2, u2;
    tr_occ of = subst_cv(g, f, bind, &f2), ou = subst_cv(g, u, bind, &u2);
    if (f2 != f || u2 != u) {
      *x2 = APP(f2, u2);
      return fire2(&R_cvh_app, of, ou, NULL);
    }
  } else if (is_app(x)) {
    tr_term f2, a2;
    tr_occ of = subst_cv(g, arg(x, 0), bind, &f2), oa = subst_cv(g, arg(x, 1), bind, &a2);
    if (f2 != arg(x, 0) || a2 != arg(x, 1)) {
      *x2 = APP(f2, a2);
      return fire2(&R_cvh_app, of, oa, NULL);
    }
  } else if (is_pi(x) || is_lam(x)) {
    tr_term d = arg(x, 0), d2 = d, b2;
    tr_occ od = is_pi(x) ? subst_cv(g, d, bind, &d2) : 0;
    hlist inner = {0};
    hlist_under(g, d, bind, &inner);
    tr_occ ob = subst_cv(CONS(d, g), arg(x, 1), &inner, &b2);
    free(inner.v);
    if (d2 != d || b2 != arg(x, 1)) {
      if (is_pi(x)) {
        *x2 = PI(d2, b2);
        return fire2(&R_cvh_pi, od, ob, NULL);
      }
      *x2 = LAM(d, b2);
      return fire1(&R_cvh_lam, ob, &d);
    }
  }
  *x2 = x;
  return cv_refl(g, x);
}

/* x with the substitution applied until it settles, then in normal form: cv(g, x, x'). */
static tr_occ cv_norm(tr_term g, tr_term x, const hlist *bind, tr_term *out) {
  tr_occ o = cv_refl(g, x);
  for (int round = 0; round < 3; round++) {
    tr_term x2;
    tr_occ o1 = subst_cv(g, x, bind, &x2);
    if (x2 == x) break;
    o = cv_trans(o, o1), x = x2;
  }
  tr_term n;
  tr_occ r = snf_pos(x, &n);
  *out = n;
  return cv_trans(o, cv_of_rd(g, r));
}

/* x == y by the hypotheses left as equations: syntactic, through applications (Dedukti's
 * term_eq_under_cstr), with conversion at the leaves. */
static tr_occ cv_match(tr_term g, tr_term x, tr_term y, const hlist *rest, int depth) {
  tr_occ o = conv_pos(x, y);
  if (o) return cv_conv(g, o);
  for (size_t i = 0; i < rest->n; i++) {
    if (rest->v[i].a == x && rest->v[i].b == y) return rest->v[i].o;
    if (rest->v[i].a == y && rest->v[i].b == x) return cv_sym(rest->v[i].o);
  }
  if (depth < 64 && is_app(x) && is_app(y)) {
    tr_occ of = cv_match(g, arg(x, 0), arg(y, 0), rest, depth + 1);
    tr_occ oa = of ? cv_match(g, arg(x, 1), arg(y, 1), rest, depth + 1) : 0;
    if (oa) return fire2(&R_cvh_app, of, oa, NULL);
  }
  if (depth < 64 && ((is_pi(x) && is_pi(y)) || (is_lam(x) && is_lam(y)))) {
    tr_term d = arg(x, 0);
    tr_occ od = is_pi(x) ? cv_match(g, d, arg(y, 0), rest, depth + 1) : 1;
    if (!od) return 0;
    hlist inner = {0};
    hlist_under(g, d, rest, &inner);
    tr_occ ob = cv_match(CONS(d, g), arg(x, 1), arg(y, 1), &inner, depth + 1);
    free(inner.v);
    if (!ob) return 0;
    if (is_pi(x)) return fire2(&R_cvh_pi, od, ob, NULL);
    tr_term d2 = arg(y, 0);
    return fire1(&R_cvh_lam, ob, &d2);
  }
  return 0;
}

/* Dedukti's use of the constraints: the hypotheses of g, in normal form and decomposed at static
 * heads, give a substitution `bind` for the pattern variables they solve and leave the others as
 * equations `rest`; each entry carries its fact cv(g, a, b). */
static void hyp_closure(tr_term g, hlist *bind_out, hlist *rest_out) {
  hlist hs = {0}, eqs = {0}, bind = {0}, rest = {0};
  hyps_in(g, &hs);
  for (size_t i = 0; i < hs.n; i++) { /* normal forms: cv(g, na, nb) */
    tr_term na, nb;
    tr_occ ra = snf_pos(hs.v[i].a, &na), rb = snf_pos(hs.v[i].b, &nb);
    tr_occ c = cv_trans(cv_sym(cv_of_rd(g, ra)), cv_trans(hs.v[i].o, cv_of_rd(g, rb)));
    decompose(g, na, nb, c, &eqs);
  }
  for (int round = 0; round < 4; round++) { /* Dedukti's solver loop: solve, substitute, again */
    size_t solved = bind.n;
    for (size_t i = 0; i < eqs.n; i++) { /* a variable solved, oriented from the variable */
      uint32_t k;
      bool seen = false;
      tr_term v = is_var(eqs.v[i].a, &k) ? eqs.v[i].a : is_var(eqs.v[i].b, &k) ? eqs.v[i].b : TR_NONE;
      for (size_t j = 0; v != TR_NONE && j < bind.n; j++) seen |= bind.v[j].a == v;
      tr_term t = TR_NONE, t2;
      tr_occ ot = 0;
      if (v != TR_NONE && !seen) {
        t = v == eqs.v[i].a ? eqs.v[i].b : eqs.v[i].a;
        ot = v == eqs.v[i].a ? eqs.v[i].o : cv_sym(eqs.v[i].o); /* cv(g, v, t) */
        /* kept idempotent: the solution under the solutions so far, and never mentioning v (an
         * equation v == t[v] is not a solution: Dedukti's occurs check) */
        tr_occ o2 = subst_cv(g, t, &bind, &t2);
        uint8_t occ = 0;
        is_var(v, &k);
        if (bl_free_bound(B, t2) > k) {
          uint8_t *mk = xr(NULL, k + 2);
          memset(mk, 0, k + 2);
          fv_mark(t2, 0, mk, k + 1);
          occ = mk[k];
          free(mk);
        }
        if (occ) t = TR_NONE;
        else {
          ot = cv_trans(ot, o2), t = t2;
          hlist one = {0};
          hpush(&one, v, t, ot);
          for (size_t j = 0; j < bind.n; j++) { /* earlier solutions rewritten by this one */
            tr_term b2;
            tr_occ ob = subst_cv(g, bind.v[j].b, &one, &b2);
            bind.v[j].o = cv_trans(bind.v[j].o, ob), bind.v[j].b = b2;
          }
          free(one.v);
        }
      }
      if (t != TR_NONE) hpush(&bind, v, t, ot);
      else hpush(&rest, eqs.v[i].a, eqs.v[i].b, eqs.v[i].o);
    }
    eqs.n = 0;
    /* the substitution applied to the equations left, normal forms, decomposed again */
    hlist again = {0};
    for (size_t i = 0; i < rest.n; i++) {
      tr_term a2, b2;
      tr_occ oa = cv_norm(g, rest.v[i].a, &bind, &a2), ob = cv_norm(g, rest.v[i].b, &bind, &b2);
      decompose(g, a2, b2, cv_trans(cv_sym(oa), cv_trans(rest.v[i].o, ob)), &again); /* a2 == a == b == b2 */
    }
    rest.n = 0;
    if (bind.n == solved || round == 3) { /* nothing new solved: what is left stays as equations */
      for (size_t i = 0; i < again.n; i++) hpush(&rest, again.v[i].a, again.v[i].b, again.v[i].o);
      free(again.v);
      break;
    }
    for (size_t i = 0; i < again.n; i++) hpush(&eqs, again.v[i].a, again.v[i].b, again.v[i].o);
    free(again.v);
  }
  /* higher-order solutions: an equation between abstractions, at its bound variable and
   * decomposed, may read X z == t; abstracted back, (z => X z) == (z => t) solves X where it is
   * applied (subst_cv) */
  for (size_t i = 0, nrest = rest.n; i < nrest; i++) {
    if (!is_lam(rest.v[i].a) || !is_lam(rest.v[i].b)) continue;
    tr_term dom = arg(rest.v[i].a, 0);
    hlist one = {0}, inner = {0};
    hpush(&one, rest.v[i].a, rest.v[i].b, rest.v[i].o);
    hlist_under(g, dom, &one, &inner);
    for (size_t j = 1; j < inner.n; j++) {
      for (int side = 0; side < 2; side++) {
        tr_term p = side ? inner.v[j].b : inner.v[j].a, q = side ? inner.v[j].a : inner.v[j].b;
        uint32_t k;
        if (!is_app(p) || arg(p, 1) != VAR(0) || !is_var(arg(p, 0), &k) || k < 1) continue;
        tr_occ oi = side ? cv_sym(inner.v[j].o) : inner.v[j].o; /* cv(cons(dom, g), p, q) */
        hpush(&bind, LAM(dom, p), LAM(dom, q), fire1(&R_cvh_lam, oi, &dom));
        break;
      }
    }
    free(one.v), free(inner.v);
  }
  free(hs.v), free(eqs.v);
  *bind_out = bind, *rest_out = rest;
}

/* cv(g, x, y): conversion, else by the hypotheses' closure: the substitution applied to both
 * sides, then normal forms, then the equations left. */
static tr_occ cv_of(tr_term g, tr_term x, tr_term y) {
  tr_occ o = conv_pos(x, y);
  if (o) return cv_conv(g, o);
  if (!has_hyp(g)) return 0;
  hlist bind, rest;
  hyp_closure(g, &bind, &rest);
  /* the goal as it stands against the equations left (a higher-order solution, one of several,
   * could rewrite it past them), then under the substitution */
  o = cv_match(g, x, y, &rest, 0);
  if (!o) {
    tr_occ ox = cv_norm(g, x, &bind, &x), oy = cv_norm(g, y, &bind, &y);
    tr_occ mid = cv_match(g, x, y, &rest, 0);
    if (mid) o = cv_trans(ox, cv_trans(mid, cv_sym(oy))); /* x0 == x == y == y0 */
  }
  free(bind.v), free(rest.v);
  return o;
}

/* A firing of a rule that reads head(t, cst(K), n), then static(K) (not under fault 6), then
 * possibly one more fact o. */
static tr_occ fire_static_head(const rk_rule *r, tr_occ oh, uint32_t k, tr_occ o) {
  tr_occ os[3];
  size_t n = 0;
  os[n++] = oh;
  if (FAULT != 6) os[n++] = SY[k].stat;
  if (o) os[n++] = o;
  return fire(r, os, NULL);
}
static bool rigid_head(uint32_t k) { return SY[k].stat || FAULT == 6; }

/* rocc(v, t): v inside t along applications headed by static symbols and abstractions (t is not
 * v). */
static tr_occ rocc_of(tr_term v, tr_term t) {
  deep();
  uint32_t n, k;
  if (is_lam(t)) {
    tr_term v2, d = arg(t, 0);
    tr_occ oe = bl_ev(B, v, SH, &v2);
    if (!oe) return 0;
    if (arg(t, 1) == v2) return is_var(v, &k) ? fire1(&R_rocc_lam_here, oe, &d) : 0;
    tr_occ o = rocc_of(v2, arg(t, 1));
    return o ? fire2(&R_rocc_lam, oe, o, &d) : 0;
  }
  if (!is_app(t) || !is_cst(spine(t, &n), &k) || !rigid_head(k)) return 0;
  tr_occ oh = head_of(t);
  if (!oh) return 0;
  if (arg(t, 1) == v) return fire_static_head(&R_rocc_here, oh, k, 0);
  tr_occ o = rocc_of(v, arg(t, 1));
  if (o) return fire_static_head(&R_rocc_arg, oh, k, o);
  o = rocc_of(v, arg(t, 0));
  return o ? fire_static_head(&R_rocc_fun, oh, k, o) : 0;
}

/* rshape(t, s) when t's top is rigid: a static spine, a product, Type or Kind. */
static tr_occ rshape_of(tr_term t) {
  uint32_t n, k;
  if (is_pi(t)) {
    tr_term v[2] = {arg(t, 0), arg(t, 1)};
    return fire(&R_rshape_pi, NULL, v);
  }
  if (t == TYPE || t == KIND) return fire(&R_rshape_sort[t == KIND], NULL, NULL);
  if (!is_cst(spine(t, &n), &k) || !rigid_head(k)) return 0;
  tr_occ oh = head_of(t);
  return oh ? fire_static_head(&R_rshape_cst, oh, k, 0) : 0;
}

static void print_term(FILE *out, tr_term t, uint32_t depth);
static bool cst_headed(tr_term t, tr_occ *o);

/* ev(v1, sh, v), v1 being v moved down past var(0) (which v does not mention), or 0. */
static tr_occ shift_of(tr_term v, tr_term *v1) {
  tr_term u, back;
  if (!bl_ev(B, v, bl_rho(B, 1, NULL, 0), &u)) return 0;
  tr_occ o = bl_ev(B, u, SH, &back);
  if (!o || back != v) return 0;
  *v1 = u;
  return o;
}

/* An equation cv(G, a, b) (fact o) under `depth` binders of g's pattern abstractions (G is g
 * extended by them): a rigid clash, or the innermost binder var(0) as one side, or inside it along
 * static heads, with the other side a shift; else, abstracted once (x => a == x => b), the same at
 * the binder further out; else, between two abstractions, deeper.  The nosol made is lifted to g. */
static tr_occ nosol_lift(tr_occ o, uint32_t times) {
  while (o && times--) o = fire1(&R_nosol_up, o, NULL);
  return o;
}
static tr_occ nosol_under(tr_term G, tr_term a, tr_term b, tr_occ o, uint32_t depth) {
  deep();
  tr_occ out = 0;
  tr_occ sa = rshape_of(a), sb = sa ? rshape_of(b) : 0;
  if (sb && A_(sa, 1) != A_(sb, 1)) return nosol_lift(fire3(&R_nosol, o, sa, sb, NULL), depth);
  if (depth == 0 && (a == TYPE) != (b == TYPE)) { /* Type against a constant-headed term typed by Type */
    tr_term y = a == TYPE ? b : a, t;
    tr_occ ohy;
    tr_occ oty = cst_headed(y, &ohy) ? infer(G, y, &t) : 0, oct = oty ? cv_of(G, t, TYPE) : 0;
    if (oct) {
      tr_occ os[4] = {a == TYPE ? o : cv_sym(o), oty, oct, ohy};
      out = fire(&R_nosol_sort, os, NULL);
      if (out) return out;
    }
  }
  for (uint32_t up = 0; !out && up < depth; up++) { /* the binder `up` levels out, as var(0) */
    for (int side = 0; side < 2 && !out; side++) {
      tr_term u = side ? b : a, v = side ? a : b, v1;
      tr_occ ouv = side ? cv_sym(o) : o, ev = shift_of(v, &v1);
      if (!ev) continue;
      if (u == VAR(0)) out = fire2(&R_nosol_bindv, ouv, ev, NULL);
      else {
        tr_occ r = rocc_of(VAR(0), u);
        if (r) out = fire3(&R_nosol_bindo, ouv, r, ev, NULL);
      }
    }
    if (out) out = nosol_lift(out, depth - 1 - up);
    else if (up + 1 < depth) { /* abstract once: x => a == x => b, one binder out */
      tr_term d = arg(G, 0);
      o = fire1(&R_cvh_lam, o, &d);
      a = LAM(d, a), b = LAM(d, b), G = arg(G, 1);
    }
  }
  return out;
}
/* a == b (fact o) decomposed at static heads, every argument (injectivity), into out. */
static void decompose_full(tr_term a, tr_term b, tr_occ o, hlist *out) {
  deep();
  uint32_t na, nb, k1, k2;
  tr_term ha = spine(a, &na), hb = spine(b, &nb);
  if (na && na == nb && is_cst(ha, &k1) && is_cst(hb, &k2) && k1 == k2 && SY[k1].stat) {
    tr_occ os[4] = {o, head_of(arg(a, 0)), head_of(arg(b, 0)), SY[k1].stat};
    tr_occ oarg = fire(&R_cv_dec[0][0], os, NULL), ofun = fire(&R_cv_dec[0][1], os, NULL);
    if (oarg && ofun) {
      decompose_full(arg(a, 1), arg(b, 1), oarg, out);
      decompose_full(arg(a, 0), arg(b, 0), ofun, out);
      return;
    }
  }
  if (a != b) hpush(out, a, b, o);
}

enum { NOSOL_DEPTH = 8 };
/* The equation a == b at G, `depth` binders over g, with the binder var(j) replaced by var(j2):
 * abstracted out to g, weakened back to G, applied to the binders' variables (var(j2) in var(j)'s
 * place) and normalized.  Returns cv(G, a', b') with a', b' in *a2, *b2, or 0. */
static tr_occ eq_instance(tr_term G, uint32_t depth, tr_term a, tr_term b, tr_occ o, uint32_t j, uint32_t j2,
                          tr_term *a2, tr_term *b2) {
  tr_term doms[NOSOL_DEPTH], Gk = G;
  for (uint32_t k = 0; k < depth; k++) { /* innermost binder first */
    tr_term d = doms[k] = arg(Gk, 0);
    o = fire1(&R_cvh_lam, o, &d);
    if (!o) return 0;
    a = LAM(d, a), b = LAM(d, b), Gk = arg(Gk, 1);
  }
  for (uint32_t k = depth; k-- > 0;) { /* back, outermost binder first */
    tr_term d = doms[k], sa, sb;
    tr_occ oa = bl_ev(B, a, SH, &sa), ob = bl_ev(B, b, SH, &sb);
    o = oa && ob ? fire3(&R_cv_wk_cons, o, oa, ob, &d) : 0;
    if (!o) return 0;
    a = sa, b = sb;
  }
  for (uint32_t i = depth; i-- > 0;) { /* the outermost abstraction takes var(depth - 1) */
    tr_term v = VAR(i == j ? j2 : i);
    o = fire2(&R_cvh_app, o, cv_refl(G, v), NULL);
    if (!o) return 0;
    a = APP(a, v), b = APP(b, v);
  }
  tr_occ ra = snf_pos(a, a2), rb = snf_pos(b, b2);
  return cv_trans(cv_sym(cv_of_rd(G, ra)), cv_trans(o, cv_of_rd(G, rb)));
}

/* The equations eqs at G, `depth` binders over g, decomposed: a refutation of one of them; else,
 * for a unary higher-order pattern X var(j) == t, its instance at another binder var(j2) against
 * an equation X var(j2) == t2, i.e. t[var(j2)/var(j)] == t2, refuted; else deeper, between two
 * abstractions. */
static tr_occ nosol_level(tr_term G, const hlist *eqs, uint32_t depth) {
  deep();
  tr_occ out = 0;
  for (size_t i = 0; i < eqs->n && !out; i++) {
    if (getenv("DK_REF_TRACE")) {
      fprintf(stderr, "dk_ref: refuting, under %u binders: ", depth);
      print_term(stderr, eqs->v[i].a, 0), fputs(" == ", stderr), print_term(stderr, eqs->v[i].b, 0), fputc('\n', stderr);
    }
    out = nosol_under(G, eqs->v[i].a, eqs->v[i].b, eqs->v[i].o, depth);
  }
  for (size_t i = 0; i < eqs->n && !out && depth; i++)
    for (int s = 0; s < 2 && !out; s++) {
      tr_term p = s ? eqs->v[i].b : eqs->v[i].a, t = s ? eqs->v[i].a : eqs->v[i].b;
      uint32_t k, j;
      if (!is_app(p) || !is_var(arg(p, 0), &k) || k < depth || !is_var(arg(p, 1), &j) || j >= depth) continue;
      for (size_t i2 = 0; i2 < eqs->n && !out; i2++)
        for (int s2 = 0; s2 < 2 && !out; s2++) {
          tr_term p2 = s2 ? eqs->v[i2].b : eqs->v[i2].a, t2 = s2 ? eqs->v[i2].a : eqs->v[i2].b, a2, b2;
          uint32_t j2;
          if (!is_app(p2) || arg(p2, 0) != arg(p, 0) || !is_var(arg(p2, 1), &j2) || j2 >= depth || j2 == j) continue;
          tr_occ oi = eq_instance(G, depth, p, t, s ? cv_sym(eqs->v[i].o) : eqs->v[i].o, j, j2, &a2, &b2);
          if (!oi || a2 != p2) continue; /* oi: cv(G, p2, t') */
          tr_occ ot = cv_trans(cv_sym(oi), s2 ? cv_sym(eqs->v[i2].o) : eqs->v[i2].o); /* t' == p2 == t2 */
          hlist sub = {0};
          decompose_full(b2, t2, ot, &sub);
          for (size_t q = 0; q < sub.n && !out; q++) out = nosol_under(G, sub.v[q].a, sub.v[q].b, sub.v[q].o, depth);
          free(sub.v);
        }
    }
  for (size_t i = 0; i < eqs->n && !out && depth + 1 < NOSOL_DEPTH; i++) {
    if (!is_lam(eqs->v[i].a) || !is_lam(eqs->v[i].b)) continue;
    hlist one = {0}, inner = {0}, next = {0};
    tr_term d = arg(eqs->v[i].a, 0);
    hpush(&one, eqs->v[i].a, eqs->v[i].b, eqs->v[i].o);
    hlist_under(G, d, &one, &inner);
    for (size_t q = 1; q < inner.n; q++) decompose_full(inner.v[q].a, inner.v[q].b, inner.v[q].o, &next);
    out = nosol_level(CONS(d, G), &next, depth + 1);
    free(one.v), free(inner.v), free(next.v);
  }
  return out;
}

/* A refutation of g's hypotheses, from the equations their closure leaves: nosol (two rigid tops
 * that differ, at g or under the binders of abstractions equated) first, the stronger statement,
 * else nowf (a variable inside the other side along static heads); 0 when neither is found.  The
 * C proposes; the facts are made by firings. */
static tr_occ refute_hyps(tr_term g) {
  hlist bind, rest, eqs = {0};
  hyp_closure(g, &bind, &rest);
  for (size_t i = 0; i < rest.n; i++) decompose_full(rest.v[i].a, rest.v[i].b, rest.v[i].o, &eqs);
  tr_occ out = nosol_level(g, &eqs, 0);
  free(eqs.v);
  for (size_t i = 0; i < rest.n && !out; i++) {
    uint32_t k;
    tr_term a = rest.v[i].a, b = rest.v[i].b, v = a;
    tr_occ r = is_var(a, &k) ? rocc_of(a, b) : 0, ov = rest.v[i].o; /* ov: cv(g, v, t) */
    if (!r && is_var(b, &k) && (r = rocc_of(b, a)) != 0) ov = cv_sym(rest.v[i].o), v = b;
    if (!r) continue;
    if (LIE == 5) ov = cv_refl(g, v); /* lie 5: v == v offered for v == t */
    out = fire2(&R_nowf, ov, r, NULL);
    if (!out && LIE) fprintf(stderr, "dk_ref: the step refused a refutation firing (a lie)\n");
  }
  free(bind.v), free(rest.v);
  return out;
}

static tr_occ tys_of(tr_term g, tr_term a, bool allow_kind, tr_term *sort) {
  tr_term t;
  tr_occ o = infer(g, a, &t);
  if (!o) return 0;
  tr_occ oc = cv_of(g, t, TYPE);
  if (oc) {
    if (sort) *sort = TYPE;
    return fire2(&R_tys[0], o, oc, NULL);
  }
  if (!allow_kind) return 0;
  oc = cv_of(g, t, KIND);
  if (oc) {
    if (sort) *sort = KIND;
    return fire2(&R_tys[1], o, oc, NULL);
  }
  return 0;
}

static tr_occ ctx_of(tr_term g) {
  ment *e = map_find(&M_ctx, g + 1);
  if (e) return e->occ;
  tr_occ o = 0;
  if (g == NIL) o = fire(&R_ctx_nil, NULL, NULL);
  else if (is_hyp(g)) {
    tr_occ og = ctx_of(arg(g, 2));
    tr_term v[2] = {arg(g, 0), arg(g, 1)};
    if (og) o = fire1(&R_ctx_hyp, og, v);
  } else {
    /* an entry may be a type of either sort: rule contexts bind variables over types; the
     * lambda-Pi restriction on abstraction is in the product and abstraction rules */
    tr_occ og = ctx_of(arg(g, 1));
    tr_term s;
    tr_occ oa = og ? tys_of(arg(g, 1), arg(g, 0), true, &s) : 0;
    if (oa) o = fire2(&R_ctx_cons[s == KIND], og, oa, NULL);
  }
  map_put(&M_ctx, g + 1)->occ = o;
  return o;
}

static tr_occ lookup_of(tr_term g, uint32_t n) {
  ment *e = map_find(&M_lookup, K2(g, n));
  if (e) return e->occ;
  tr_occ o = 0;
  if (g != NIL && is_hyp(g)) {
    tr_occ ol = lookup_of(arg(g, 2), n);
    tr_term v[2] = {arg(g, 0), arg(g, 1)};
    if (ol) o = fire1(&R_lookup_hyp, ol, v);
  } else if (g != NIL) {
    if (n == 0) {
      tr_occ oe = bl_ev(B, arg(g, 0), SH, NULL);
      tr_term gg = arg(g, 1);
      if (oe) o = fire1(&R_lookup0, oe, &gg);
    } else {
      tr_occ ol = lookup_of(arg(g, 1), n - 1);
      tr_occ oe = ol ? bl_ev(B, A_(ol, 2), SH, NULL) : 0;
      tr_term bb = arg(g, 0);
      if (oe) o = fire2(&R_lookupS, ol, oe, &bb);
    }
  }
  map_put(&M_lookup, K2(g, n))->occ = o;
  return o;
}

static tr_term infer_fail_type; /* for messages */

static tr_occ infer(tr_term g, tr_term t, tr_term *ty) {
  deep();
  ment *e = map_find(&M_ty, K2(g, t));
  if (e && (e->occ || e->stamp == epoch_no)) {
    if (e->occ) *ty = A_(e->occ, 2);
    return e->occ;
  }
  tr_occ o = 0;
  uint32_t k;
  if (t == TYPE) {
    tr_occ oc = ctx_of(g);
    if (oc) o = fire1(&R_ty_type, oc, NULL);
  } else if (is_cst(t, &k)) {
    tr_occ oc = ctx_of(g);
    if (oc && SY[k].decl) o = fire2(&R_ty_cst, oc, SY[k].decl, NULL);
  } else if (is_var(t, &k)) {
    tr_occ oc = ctx_of(g), ol = oc ? lookup_of(g, k) : 0;
    if (ol) o = fire2(&R_ty_var, oc, ol, NULL);
  } else if (is_pi(t)) {
    tr_term sd, sc;
    tr_occ od = tys_of(g, arg(t, 0), COC, &sd);
    tr_term g2 = CONS(arg(t, 0), g);
    tr_occ ob = od && ctx_of(g2) ? tys_of(g2, arg(t, 1), true, &sc) : 0;
    if (ob) o = fire2(&R_ty_pi[sd == KIND][sc == KIND], od, ob, NULL);
  } else if (is_lam(t) && arg(t, 0) != NONE) {
    tr_term sd, bt;
    tr_occ od = tys_of(g, arg(t, 0), COC, &sd);
    tr_term g2 = CONS(arg(t, 0), g);
    tr_occ ob = od && ctx_of(g2) ? infer(g2, arg(t, 1), &bt) : 0;
    if (ob && bt != KIND) o = fire2(&R_ty_lam[sd == KIND], od, ob, NULL);
  } else if (is_app(t)) {
    tr_term p, w;
    tr_occ of = infer(g, arg(t, 0), &p);
    if (of) {
      tr_occ ow = whnf_pos(p, &w);
      if (is_pi(w)) {
        tr_occ ocw = cv_conv(g, w == p ? fire(&R_cv_refl, NULL, &p) : fire2(&R_cv_redl, ow, fire(&R_cv_refl, NULL, &w), NULL));
        tr_occ oconv = 0, ou;
        tr_term at;
        if (FAULT == 1) ou = is_lam(arg(t, 1)) ? check(g, arg(t, 1), arg(w, 0), &oconv) : infer(g, arg(t, 1), &at);
        else ou = check(g, arg(t, 1), arg(w, 0), &oconv);
        if (LIE == 1 && ou) oconv = ocw;
        tr_occ oe = ou ? bl_ev(B, arg(w, 1), bl_cs(B, arg(t, 1), ID), NULL) : 0;
        if (oe) {
          tr_occ os[5] = {of, ocw, ou, oconv, oe};
          if (FAULT == 1) os[3] = oe;
          o = fire(&R_ty_app, os, NULL);
          if (!o && LIE) fprintf(stderr, "dk_ref: the step refused an application firing (a lie)\n");
        }
      } else
        infer_fail_type = w;
    }
  }
  e = map_put(&M_ty, K2(g, t));
  e->occ = o, e->stamp = epoch_no;
  if (o) *ty = A_(o, 2);
  return o;
}

/* ty(g, t, T) with conv(T, want), or 0. */
static tr_term check_fail_have, check_fail_want, check_fail_g;
static tr_occ check(tr_term g, tr_term t, tr_term want, tr_occ *conv) {
  deep();
  tr_occ o = 0;
  tr_term ty;
  if (is_lam(t)) {
    tr_term w;
    whnf_pos(want, &w);
    if (is_pi(w)) {
      tr_term dom = arg(t, 0) != NONE ? arg(t, 0) : arg(w, 0), sd, bt;
      tr_occ od = tys_of(g, dom, COC, &sd);
      tr_term g2 = CONS(dom, g);
      tr_occ oc2, ob = od && ctx_of(g2) ? check(g2, arg(t, 1), arg(w, 1), &oc2) : 0;
      if (ob) {
        bt = A_(ob, 2);
        if (bt != KIND) o = fire2(arg(t, 0) != NONE ? &R_ty_lam[sd == KIND] : &R_ty_lamn[sd == KIND], od, ob, NULL);
      }
    }
    if (!o && arg(t, 0) == NONE) return 0;
    if (!o) o = infer(g, t, &ty);
  } else
    o = infer(g, t, &ty);
  if (!o) return 0;
  ty = A_(o, 2);
  *conv = cv_of(g, ty, want);
  if (!*conv) {
    check_fail_have = ty, check_fail_want = want, check_fail_g = g;
    return 0;
  }
  return o;
}

/* ============================================================================================
 * Printing (for #EVAL, #INFER and messages).
 * ========================================================================================== */

static void print_term(FILE *out, tr_term t, uint32_t depth) {
  uint32_t k;
  if (t == TYPE) fputs("Type", out);
  else if (t == KIND) fputs("Kind", out);
  else if (is_var(t, &k)) {
    if (k < depth) fprintf(out, "x%u", depth - 1 - k);
    else fprintf(out, "free%u", k - depth);
  } else if (is_cst(t, &k)) {
    const char *dot = strchr(SY[k].name, '.');
    fputs(dot ? dot + 1 : SY[k].name, out);
  } else if (is_app(t)) {
    uint32_t n;
    tr_term h = spine(t, &n);
    fputc('(', out);
    print_term(out, h, depth);
    for (uint32_t i = 0; i < n; i++) fputc(' ', out), print_term(out, spine_arg(t, n, i), depth);
    fputc(')', out);
  } else if (is_lam(t)) {
    fprintf(out, "(x%u", depth);
    if (arg(t, 0) != NONE) fputs(" : ", out), print_term(out, arg(t, 0), depth);
    fputs(" => ", out);
    print_term(out, arg(t, 1), depth + 1);
    fputc(')', out);
  } else if (is_pi(t)) {
    fprintf(out, "(x%u : ", depth);
    print_term(out, arg(t, 0), depth);
    fputs(" -> ", out);
    print_term(out, arg(t, 1), depth + 1);
    fputc(')', out);
  } else
    tr_print(out, C, t);
}

/* ============================================================================================
 * The reader: tokens.
 * ========================================================================================== */

enum {
  K_EOF, K_ID, K_QID, K_TYPE, K_DEF, K_DEFAC, K_DEFACU, K_INJ, K_THM, K_PRV, K_DOT, K_COMMA, K_COLON, K_EQUAL, K_LSQ,
  K_RSQ, K_LBRA, K_RBRA, K_LPAR, K_RPAR, K_LONG, K_ARROW, K_FAT, K_DEFEQ, K_NAME, K_REQUIRE, K_EVAL, K_INFER, K_CHECK,
  K_CHECKNOT, K_ASSERT, K_ASSERTNOT, K_PRINT, K_GDT, K_PRAGMA, K_STRING
};
typedef struct {
  int kind;
  char *text; /* K_ID, K_QID (module.id), K_STRING, K_PRAGMA */
  uint32_t line;
} token;

static const char *src;
static size_t pos, len;
static uint32_t line;
static token tk;          /* the current token */
static char *module_name; /* the current module */

static bool letter(unsigned char c) {
  return isalnum(c) || c == '_' || c == '!' || c == '?' || c == '\'' || c == '+' || c == '*' || c == '~' || c == '&' ||
         c == '^' || c == '@' || c == '=' || c == '$' || c == '%' || c == '/' || c == '<' || c == '|' || c == '-' ||
         c == '\\' || c == '>';
}
static bool mletter(unsigned char c) { return isalnum(c) || c == '_'; }
static char *dupn(const char *s, size_t n) {
  char *d = xr(NULL, n + 1);
  memcpy(d, s, n);
  d[n] = 0;
  return d;
}

/* Just past the escaped identifier {|...|} that starts at p. */
static size_t escaped_end(size_t p) {
  size_t j = p + 2;
  while (j + 1 < len && !(src[j] == '|' && src[j + 1] == '}')) {
    if (src[j] == '\n') cur_line = line, refuse(BY_READER, "a new line in an identifier");
    j++;
  }
  if (j + 1 >= len) cur_line = line, refuse(BY_READER, "unexpected end of file in an identifier");
  return j + 2;
}

static void next(void) {
  free(tk.text);
  tk.text = NULL;
  for (;;) {
    while (pos < len && (src[pos] == ' ' || src[pos] == '\t' || src[pos] == '\r' || src[pos] == '\n'))
      line += src[pos++] == '\n';
    if (pos + 1 < len && src[pos] == '(' && src[pos + 1] == ';') {
      int depth = 0;
      pos += 2;
      for (;;) {
        if (pos >= len) cur_line = line, refuse(BY_READER, "unexpected end of file in a comment");
        if (src[pos] == '\n') line++;
        if (pos + 1 < len && src[pos] == ';' && src[pos + 1] == ')') {
          pos += 2;
          if (depth-- == 0) break;
          continue;
        }
        if (pos + 1 < len && src[pos] == '(' && src[pos + 1] == ';') {
          depth++, pos += 2;
          continue;
        }
        pos++;
      }
      continue;
    }
    break;
  }
  tk.line = line;
  if (pos >= len) {
    tk.kind = K_EOF;
    return;
  }
  /* the longest identifier from here, and a qualified one */
  size_t id = 0;
  while (pos + id < len && letter((unsigned char)src[pos + id])) id++;
  size_t md = 0;
  while (pos + md < len && mletter((unsigned char)src[pos + md])) md++;
  size_t qid = 0;
  if (md && pos + md < len && src[pos + md] == '.') {
    size_t j = 0;
    while (pos + md + 1 + j < len && letter((unsigned char)src[pos + md + 1 + j])) j++;
    if (j) qid = md + 1 + j;
  }
  static const struct {
    const char *s;
    int k;
  } fixed[] = {{"-->", K_LONG}, {"->", K_ARROW}, {"=>", K_FAT}, {":=", K_DEFEQ}, {"==", K_EQUAL}, {".", K_DOT},
               {",", K_COMMA}, {":", K_COLON}, {"[", K_LSQ}, {"]", K_RSQ}, {"{", K_LBRA}, {"}", K_RBRA}, {"(", K_LPAR},
               {")", K_RPAR}, {"Type", K_TYPE}, {"defacu", K_DEFACU}, {"defac", K_DEFAC}, {"def", K_DEF},
               {"injective", K_INJ}, {"thm", K_THM}, {"private", K_PRV}, {"require", K_REQUIRE}, {"#CHECKNOT", K_CHECKNOT},
               {"#ASSERTNOT", K_ASSERTNOT}, {"#NAME", K_NAME}, {"#REQUIRE", K_REQUIRE}, {"#EVAL", K_EVAL},
               {"#INFER", K_INFER}, {"#CHECK", K_CHECK}, {"#ASSERT", K_ASSERT}, {"#PRINT", K_PRINT}, {"#GDT", K_GDT}};
  size_t best = 0;
  int bk = -1;
  for (size_t f = 0; f < sizeof fixed / sizeof *fixed; f++) {
    size_t n = strlen(fixed[f].s);
    if (n > best && pos + n <= len && !memcmp(src + pos, fixed[f].s, n)) best = n, bk = fixed[f].k;
  }
  /* qualified names: M.id, M.{|id|}, {|M|}.id, {|M|}.{|id|} (an escaped module is named without
   * its braces, an escaped identifier keeps them); {|id|} alone is an identifier */
  bool esc = src[pos] == '{' && pos + 1 < len && src[pos + 1] == '|';
  size_t mend = esc ? escaped_end(pos) : (md ? pos + md : 0); /* just past the module part */
  if (esc || md) {
    size_t q = 0, iend = 0;
    if (mend < len && src[mend] == '.') {
      if (mend + 2 < len && src[mend + 1] == '{' && src[mend + 2] == '|') iend = escaped_end(mend + 1);
      else {
        while (mend + 1 + q < len && letter((unsigned char)src[mend + 1 + q])) q++;
        if (q) iend = mend + 1 + q;
      }
    }
    if (iend && (esc || iend - pos > best)) {
      size_t ml = esc ? mend - pos - 4 : md, il = iend - mend - 1;
      tk.kind = K_QID;
      tk.text = xr(NULL, ml + il + 2);
      memcpy(tk.text, src + (esc ? pos + 2 : pos), ml);
      tk.text[ml] = '.';
      memcpy(tk.text + ml + 1, src + mend + 1, il);
      tk.text[ml + 1 + il] = 0;
      pos = iend;
      return;
    }
    if (esc) {
      tk.kind = K_ID;
      tk.text = dupn(src + pos, mend - pos);
      pos = mend;
      return;
    }
  }
  if (qid > best && qid >= id) {
    tk.kind = K_QID;
    tk.text = dupn(src + pos, qid);
    pos += qid;
    return;
  }
  if (id > best) {
    tk.kind = K_ID;
    tk.text = dupn(src + pos, id);
    pos += id;
    return;
  }
  if (bk >= 0) {
    tk.kind = bk;
    pos += best;
    return;
  }
  if (src[pos] == '"') {
    size_t j = pos + 1;
    while (j < len && src[j] != '"') {
      if (src[j] == '\\' && j + 1 < len) j++;
      if (src[j] == '\n') line++;
      j++;
    }
    if (j >= len) cur_line = line, refuse(BY_READER, "unexpected end of file in a string");
    tk.kind = K_STRING;
    tk.text = dupn(src + pos + 1, j - pos - 1);
    pos = j + 1;
    return;
  }
  if (src[pos] == '#') { /* a pragma, to the next '.' followed by white space or the end */
    size_t j = pos + 1;
    while (j < len && !(src[j] == '.' && (j + 1 >= len || src[j + 1] == ' ' || src[j + 1] == '\n' || src[j + 1] == '\t' ||
                                          src[j + 1] == '\r'))) {
      if (src[j] == '\n') line++;
      j++;
    }
    if (j >= len) cur_line = line, refuse(BY_READER, "unexpected end of file in a pragma");
    tk.kind = K_PRAGMA;
    tk.text = dupn(src + pos, j - pos);
    pos = j + 1;
    return;
  }
  cur_line = line;
  refuse(BY_READER, "unexpected character '%c'", src[pos]);
}

static void expect(int kind, const char *what) {
  if (tk.kind != kind) cur_line = tk.line, refuse(BY_READER, "expected %s", what);
  next();
}

/* ============================================================================================
 * The reader: terms, with names resolved (bound variables, pattern variables, constants).
 * ========================================================================================== */

typedef struct {
  char **names; /* bound variables, innermost last */
  uint32_t n, cap;
  char **pvars; /* pattern variables of the rule being read, in order (NULL: none) */
  uint32_t npv, cappv;
  bool in_pattern; /* reading a left-hand side: _ is a new pattern variable */
  bool any_bracket;
} scope;

static void push_name(scope *sc, const char *name) {
  GROW(sc->names, sc->n, sc->cap);
  sc->names[sc->n++] = strcpy(xr(NULL, strlen(name) + 1), name);
}
static void pop_name(scope *sc) { free(sc->names[--sc->n]); }

static uint32_t resolve_const(const char *name, bool qualified) {
  char *key;
  if (qualified) key = strcpy(xr(NULL, strlen(name) + 1), name);
  else {
    key = xr(NULL, strlen(module_name) + strlen(name) + 2);
    sprintf(key, "%s.%s", module_name, name);
  }
  uint32_t k = sym_find(key);
  if (k == UINT32_MAX || !SY[k].decl) {
    cur_line = tk.line;
    refuse(BY_READER, "unknown symbol %s", key);
  }
  free(key);
  return k;
}

static tr_term pterm(scope *sc);
static tr_term paterm(scope *sc);

static tr_term name_term(scope *sc, const char *name, bool qualified) {
  if (!qualified) {
    for (uint32_t i = sc->n; i-- > 0;) /* `_` binds nothing a name could refer to */
      if (strcmp(name, "_") && !strcmp(sc->names[i], name)) return VAR(sc->n - 1 - i);
    for (uint32_t i = 0; i < sc->npv; i++)
      if (sc->pvars[i] && !strcmp(sc->pvars[i], name)) return T2(f_pv, tr_code(C, i), NAT(sc->n));
    if (!strcmp(name, "_") && sc->in_pattern) {
      GROW(sc->pvars, sc->npv, sc->cappv);
      sc->pvars[sc->npv++] = NULL; /* a wildcard: a pattern variable without a name */
      return T2(f_pv, tr_code(C, sc->npv - 1), NAT(sc->n));
    }
  }
  return CST(resolve_const(name, qualified));
}

static tr_term psterm(scope *sc) {
  if (tk.kind == K_TYPE) {
    next();
    return TYPE;
  }
  if (tk.kind == K_ID || tk.kind == K_QID) {
    bool q = tk.kind == K_QID;
    char *name = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
    tr_term t = name_term(sc, name, q);
    free(name);
    next();
    return t;
  }
  if (tk.kind == K_LPAR) {
    next();
    tr_term t = pterm(sc);
    expect(K_RPAR, "')'");
    return t;
  }
  if (tk.kind == K_LBRA) { /* a bracket {t}: its variables are bound elsewhere in the pattern */
    if (!sc->in_pattern) cur_line = tk.line, refuse(BY_READER, "a bracket outside a pattern");
    sc->any_bracket = true;
    next();
    sc->in_pattern = false;
    tr_term t = pterm(sc);
    sc->in_pattern = true;
    expect(K_RBRA, "'}'");
    return T1(f_brk, t);
  }
  cur_line = tk.line;
  refuse(BY_READER, "expected a term");
  return TR_NONE;
}

static bool starts_sterm(void) {
  return tk.kind == K_TYPE || tk.kind == K_ID || tk.kind == K_QID || tk.kind == K_LPAR || tk.kind == K_LBRA;
}

static tr_term paterm(scope *sc) {
  deep();
  tr_term t = psterm(sc);
  while (starts_sterm()) t = APP(t, psterm(sc));
  return t;
}

/* Is the token after the current one `kind`?  (Restores the reader.) */
static int peek_kind(void) {
  size_t save = pos;
  uint32_t sl = line;
  token cur = tk;
  cur.text = tk.text ? strcpy(xr(NULL, strlen(tk.text) + 1), tk.text) : NULL;
  next();
  int k = tk.kind;
  free(tk.text);
  pos = save, line = sl;
  tk = cur;
  return k;
}

static tr_term pterm(scope *sc) {
  deep();
  if (tk.kind == K_ID && peek_kind() == K_FAT) { /* x => t */
    char *x = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
    next(), next();
    push_name(sc, x);
    tr_term body = pterm(sc);
    pop_name(sc);
    free(x);
    return LAM(NONE, body);
  }
  if (tk.kind == K_ID && peek_kind() == K_COLON) { /* x : A -> B   or   x : A => t */
    char *x = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
    next(), next();
    tr_term a = paterm(sc);
    int k = tk.kind;
    if (k != K_ARROW && k != K_FAT) cur_line = tk.line, refuse(BY_READER, "expected -> or =>");
    next();
    push_name(sc, x);
    tr_term b = pterm(sc);
    pop_name(sc);
    free(x);
    return k == K_ARROW ? PI(a, b) : LAM(a, b);
  }
  if (tk.kind == K_LPAR && peek_kind() == K_ID) { /* (x : A) -> B   or   (x : A := t) => u */
    size_t save = pos;
    uint32_t sl = line;
    token cur = tk;
    cur.text = NULL;
    next();
    char *x = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
    next();
    if (tk.kind == K_COLON) {
      next();
      tr_term a = paterm(sc);
      if (tk.kind == K_RPAR) {
        next();
        expect(K_ARROW, "'->'");
        push_name(sc, x);
        tr_term b = pterm(sc);
        pop_name(sc);
        free(x);
        return PI(a, b);
      }
      if (tk.kind == K_DEFEQ) {
        next();
        tr_term v = paterm(sc);
        expect(K_RPAR, "')'");
        expect(K_FAT, "'=>'");
        push_name(sc, x);
        tr_term b = pterm(sc);
        pop_name(sc);
        free(x);
        return APP(LAM(a, b), v);
      }
      if (tk.kind != K_FAT && tk.kind != K_ARROW) cur_line = tk.line, refuse(BY_READER, "expected ')' or ':='");
      /* (x : A => t) or (x : A -> B): an ordinary parenthesized term, read again below */
    }
    free(x);
    free(tk.text);
    tk = cur, pos = save, line = sl; /* an ordinary parenthesized term */
  }
  tr_term a = paterm(sc);
  if (tk.kind == K_ARROW) { /* A -> B: B is read under one more binder, which no name refers to */
    next();
    push_name(sc, "");
    tr_term b = pterm(sc);
    pop_name(sc);
    return PI(a, b);
  }
  return a;
}

/* ============================================================================================
 * Declarations, definitions, rules and commands.
 * ========================================================================================== */

static uint32_t n_decls, n_defs, n_thms, n_rules, n_asserts, n_cmds;

static tr_term known_fact(uint32_t k) {
  char *s = xr(NULL, strlen(SY[k].name) + 8);
  sprintf(s, "known.%s", SY[k].name);
  tr_term t = tr_const(C, s);
  free(s);
  return t;
}

/* A type mismatch: refused by the fact notconv(have, want) when the firings derive it. */
static void refuse_mismatch(const char *what) {
  /* under hypotheses a non-convertibility fact refutes nothing (the hypotheses may equate the
   * two), and the search for a conversion under hypotheses is not complete: no verdict */
  if (check_fail_g != TR_NONE && has_hyp(check_fail_g)) {
    /* two closed types are what they are in every instance: a non-convertibility refutes */
    if (check_fail_have != TR_NONE && check_fail_want != TR_NONE && bl_free_bound(B, check_fail_have) == 0 &&
        bl_free_bound(B, check_fail_want) == 0) {
      tr_occ o = notconv_neg(check_fail_have, check_fail_want);
      if (o) refuse(BY_FACT, "%s: two closed types, not convertible (notconv fact %llu)", what, (unsigned long long)o);
    }
    noverdict("%s: no conversion found under the typing hypotheses (that search is not complete)", what);
  }
  if (check_fail_have != TR_NONE && check_fail_want != TR_NONE) {
    tr_occ o = notconv_neg(check_fail_have, check_fail_want);
    if (o) refuse(BY_FACT, "%s: the type found is not convertible to the type expected (notconv fact %llu)", what,
                  (unsigned long long)o);
  }
  refuse(BY_ORDER, "%s: no typing found", what);
}

static uint32_t declare_symbol(const char *id) {
  char *key = xr(NULL, strlen(module_name) + strlen(id) + 2);
  sprintf(key, "%s.%s", module_name, id);
  uint32_t k = sym_find(key);
  if (k == UINT32_MAX) k = sym_add(key);
  free(key);
  return k;
}

/* A declaration or definition: kind, name, type (or TR_NONE), body (or TR_NONE). */
static void declare(int kind, const char *id, tr_term ty, tr_term body) {
  uint32_t k = declare_symbol(id);
  tr_term code = tr_code(C, k), known = known_fact(k);
  check_fail_have = check_fail_want = check_fail_g = TR_NONE;
  rk_rule r;
  rk_init(&r, "a declaration", 3); /* S0 T1 A2 */
  tr_occ occs[3];
  size_t no = 0;
  tr_term sort;
  if (ty != TR_NONE) {
    occs[no] = tys_of(NIL, ty, true, &sort);
    if (!occs[no++]) refuse_mismatch("the declared type is not a well-typed type");
    rk_read(&r, TYS(NIL, ty, L(0)));
  }
  if (body != TR_NONE) {
    if (ty != TR_NONE) {
      tr_occ oc, ob = check(NIL, body, ty, &oc);
      if (!ob) refuse_mismatch("the body does not have the declared type");
      occs[no++] = ob, occs[no++] = oc;
      rk_read(&r, TY(NIL, body, L(1)));
      rk_read(&r, T3(f_cv, NIL, L(1), ty));
    } else {
      tr_term t;
      tr_occ ob = infer(NIL, body, &t);
      if (!ob) refuse_mismatch("the body has no type");
      tr_occ os = tys_of(NIL, t, true, &sort);
      if (!os) refuse(BY_ORDER, "the type of the body is not a type");
      occs[no++] = ob, occs[no++] = os;
      rk_read(&r, TY(NIL, body, L(2)));
      rk_read(&r, TYS(NIL, L(2), L(0)));
      ty = t;
    }
  }
  rk_absent(&r, known);
  rk_make(&r, known);
  rk_make(&r, T2(f_decl, code, ty == TR_NONE ? L(2) : ty));
  if (kind == SK_STATIC || kind == SK_THM) rk_make(&r, T1(f_static, code));
  else if (kind == SK_DEFINABLE) rk_make(&r, T2(f_rules, code, NIL));
  else rk_make(&r, T2(f_defn, code, body));
  bool inj = kind == SK_DEFINABLE && decl_injective;
  if (inj) rk_make(&r, T1(f_inj, code));
  tr_occ made[4];
  if (!rk_fire(&E, &r, occs, NULL, made, NULL)) refuse(BY_FIRING, "the declaration of %s (already declared?)", id);
  rk_free(&r);
  SY[k].kind = kind;
  SY[k].decl = made[1];
  SY[k].type = A_(made[1], 1);
  if (kind == SK_STATIC || kind == SK_THM) SY[k].stat = made[2];
  else if (kind == SK_DEFINABLE) SY[k].rules = made[2];
  else SY[k].defn = made[2], SY[k].body = body;
  if (inj) SY[k].inj = made[3];
  if (kind == SK_THM) n_thms++;
  else if (body != TR_NONE) n_defs++;
  else n_decls++;
}

/* ---- rewrite rules ---- */

typedef struct {
  char *name;
  tr_term type; /* read in the scope of the earlier pattern variables (TR_NONE: none) */
} pvdecl;

/* pv(i, d) -> var(m - 1 - i + depth): the rule's pattern variables as context variables. */
static tr_term to_delta(tr_term t, uint32_t m, uint32_t depth) {
  deep();
  if (head_sym(t) == f_brk) return T1(f_brk, to_delta(arg(t, 0), m, depth));
  if (head_sym(t) == f_pv) {
    uint32_t i = (uint32_t)tr_term_code(C, arg(t, 0));
    return VAR(m - 1 - i + depth);
  }
  if (is_app(t)) return APP(to_delta(arg(t, 0), m, depth), to_delta(arg(t, 1), m, depth));
  if (is_lam(t)) return LAM(to_delta(arg(t, 0), m, depth), to_delta(arg(t, 1), m, depth + 1));
  if (is_pi(t)) return PI(to_delta(arg(t, 0), m, depth), to_delta(arg(t, 1), m, depth + 1));
  return t;
}

/* t with every bracket {u} written u: the left-hand side as a term to type. */
static tr_term strip_brk(tr_term t) {
  deep();
  if (head_sym(t) == f_brk) return arg(t, 0);
  if (is_app(t)) return APP(strip_brk(arg(t, 0)), strip_brk(arg(t, 1)));
  if (is_lam(t)) return LAM(strip_brk(arg(t, 0)), strip_brk(arg(t, 1)));
  return t;
}

static int add_node(rrule *R, tr_term t, int parent, uint32_t depth, uint32_t m) {
  deep();
  pnode n = {0};
  n.parent = parent;
  n.depth = depth;
  n.first = -1;
  int me = (int)R->nnodes;
  if (head_sym(t) == f_brk) { /* matched as a variable of arity 0, then its guard */
    n.kind = N_BRK;
    n.first = me;
    n.pv = UINT32_MAX;
    n.rho = bl_rho(B, depth, NULL, 0);
    if (!bl_ev(B, arg(t, 0), n.rho, &n.guard)) refuse(BY_READER, "a bracket mentions a variable bound in the pattern");
    R->nodes = xr(R->nodes, (R->nnodes + 1) * sizeof *R->nodes);
    R->nodes[R->nnodes++] = n;
    return me;
  }
  if (is_lam(t)) {
    n.kind = N_LAM;
    n.nargs = 1;
    n.kids = xr(NULL, sizeof *n.kids);
    R->nodes = xr(R->nodes, (R->nnodes + 1) * sizeof *R->nodes);
    R->nodes[R->nnodes++] = n;
    int kid = add_node(R, arg(t, 1), me, depth + 1, m);
    R->nodes[me].kids[0] = kid;
    return me;
  }
  uint32_t na, k;
  tr_term h = spine(t, &na);
  if (head_sym(h) == f_brk) refuse(BY_READER, "a bracket applied to arguments");
  if (is_var(h, &k) && k >= depth) { /* a pattern variable */
    n.kind = N_PVAR;
    n.pv = m - 1 - (k - depth);
    n.a = na;
    n.ys = xr(NULL, (na + 1) * sizeof *n.ys);
    for (uint32_t j = 0; j < na; j++) {
      uint32_t y;
      if (!is_var(spine_arg(t, na, j), &y) || y >= depth)
        refuse(BY_READER, "a pattern variable applied to something other than a bound variable (not a Miller pattern)");
      for (uint32_t i = 0; i < j; i++)
        if (n.ys[i] == y) refuse(BY_READER, "a pattern variable applied twice to one bound variable (not a Miller pattern)");
      n.ys[j] = y;
    }
    n.rho = bl_rho(B, depth, n.ys, na);
    R->nodes = xr(R->nodes, (R->nnodes + 1) * sizeof *R->nodes);
    R->nodes[R->nnodes++] = n;
    return me;
  }
  if (is_var(h, &k)) n.kind = N_BVAR, n.head = k;
  else if (is_cst(h, &k)) n.kind = N_CST, n.head = k;
  else refuse(BY_READER, "this is not a pattern");
  n.nargs = na;
  n.kids = xr(NULL, (na + 1) * sizeof *n.kids);
  R->nodes = xr(R->nodes, (R->nnodes + 1) * sizeof *R->nodes);
  R->nodes[R->nnodes++] = n;
  for (uint32_t j = 0; j < na; j++) {
    int kid = add_node(R, spine_arg(t, na, j), me, depth, m);
    R->nodes[me].kids[j] = kid;
  }
  return me;
}

/* ---- the proposed types of untyped pattern variables (the C proposes; firings decide) ---- */

static tr_term *bvtypes; /* types of the pattern's bound variables, innermost last */
static uint32_t nbv, capbv;
static tr_term *pvtype;

/* The type of pattern variable X ys at depth d whose occurrence has type `want` (in context
 * [delta, x_1 .. x_d]): Pi over the arguments' types, moved to delta, or TR_NONE. */
static tr_term pv_type_from(tr_term want, uint32_t depth, const uint32_t *ys, uint32_t a) {
  /* sigma_j: x_{y_k} (k < j) -> z_k, other bound x_i -> var(i + j), delta -> shifted by j */
  tr_term *doms = xr(NULL, (a + 1) * sizeof *doms), res = TR_NONE, r;
  for (uint32_t j = 0; j <= a; j++) {
    tr_term s = bl_shk(B, depth + j); /* the pattern's binders stay in scope: removed at the end */
    for (uint32_t i = depth; i-- > 0;) {
      tr_term e = VAR(i + j);
      for (uint32_t k = 0; k < j; k++)
        if (ys[k] == i) e = VAR(j - 1 - k);
      s = bl_cs(B, e, s);
    }
    tr_term src;
    if (j < a) { /* the type of x_{y_j}, at depth d */
      uint32_t y = ys[j];
      if (!bl_ev(B, bvtypes[nbv - 1 - y], bl_shk(B, y + 1), &src)) goto out;
    } else
      src = want;
    if (!bl_ev(B, src, s, &r)) goto out;
    doms[j] = r;
  }
  res = doms[a];
  for (uint32_t j = a; j-- > 0;) res = PI(doms[j], res);
  if (!bl_ev(B, res, bl_rho(B, depth, NULL, 0), &r)) res = TR_NONE;
  else res = r;
out:
  free(doms);
  return res;
}

static void walk_pattern(tr_term t, tr_term want, uint32_t depth, uint32_t m) {
  deep();
  tr_term w;
  if (is_lam(t)) {
    if (want == TR_NONE) return;
    whnf_pos(want, &w);
    if (!is_pi(w)) return;
    GROW(bvtypes, nbv, capbv);
    bvtypes[nbv++] = arg(w, 0);
    walk_pattern(arg(t, 1), arg(w, 1), depth + 1, m);
    nbv--;
    return;
  }
  uint32_t na, k;
  if (head_sym(t) == f_brk) return; /* a bracket binds no variable */
  tr_term h = spine(t, &na), ty = TR_NONE;
  if (is_var(h, &k) && k >= depth) {
    uint32_t x = m - 1 - (k - depth);
    if (pvtype[x] != TR_NONE || want == TR_NONE) return;
    uint32_t *ys = xr(NULL, (na + 1) * sizeof *ys);
    for (uint32_t j = 0; j < na; j++) {
      uint32_t y;
      if (!is_var(spine_arg(t, na, j), &y)) {
        free(ys);
        return;
      }
      ys[j] = y;
    }
    tr_term tyx = pv_type_from(want, depth, ys, na), nw;
    /* the type mentions a bound variable the pattern variable cannot depend on: Dedukti reads it
     * up to conversion (K z may reduce to a type without z) */
    if (tyx == TR_NONE && depth > 0 && snf_pos(want, &nw) && nw != want) tyx = pv_type_from(nw, depth, ys, na);
    free(ys);
    /* in delta (depth 0): var(m - 1 - x) is X itself; the proposal is kept in full delta */
    pvtype[x] = tyx;
    return;
  }
  if (is_cst(h, &k)) ty = SY[k].type;
  else if (is_var(h, &k) && k < depth) {
    if (!bl_ev(B, bvtypes[nbv - 1 - k], bl_shk(B, k + 1), &ty)) return;
  } else
    return;
  for (uint32_t j = 0; j < na; j++) {
    tr_term a = spine_arg(t, na, j);
    whnf_pos(ty, &w);
    if (!is_pi(w)) return;
    walk_pattern(a, arg(w, 0), depth, m);
    if (!bl_ev(B, arg(w, 1), bl_cs(B, strip_brk(a), ID), &ty)) return;
  }
}

/* The justification of one hypothesis of a rule's context (for just_of). */
typedef struct {
  tr_term g, x, a;     /* hyp(x, a, g) */
  tr_occ obl, sub, ev; /* oblig(g, S, x, a), sub(L, F), ev(S, shk(K), F) */
} hjust;

/* just(L, K, G), from G's bottom up; 0 when a hypothesis has no justification. */
static tr_occ just_of(tr_term lhs, uint32_t k, tr_term g, const hjust *hj, uint32_t nhj) {
  if (g == NIL) {
    tr_term v[2] = {lhs, NAT(k)};
    return fire(&R_just_nil, NULL, v);
  }
  if (is_hyp(g)) {
    tr_term below = arg(g, 2);
    tr_occ o = just_of(lhs, k, below, hj, nhj);
    for (uint32_t i = 0; o && i < nhj; i++)
      if (hj[i].g == below && hj[i].x == arg(g, 0) && hj[i].a == arg(g, 1)) {
        tr_occ occs[4] = {o, hj[i].obl, hj[i].sub, hj[i].ev};
        return fire(&R_just_hyp, occs, NULL);
      }
    return 0;
  }
  tr_occ o = just_of(lhs, k + 1, arg(g, 1), hj, nhj);
  tr_term t = arg(g, 0);
  return o ? fire1(&R_just_cons, o, &t) : 0;
}

/* The innermost application F U of the left-hand side (outside its binders) whose argument's type
 * is not convertible, under g's hypotheses, to F's domain: its fact oblig(g, lhs, X, A), or 0. */
/* An application F U whose argument's type is not F's domain, but where F or U has a pattern
 * variable at its head: no obligation can be made there (R_oblig); the last one met, for the
 * caller (an annotation the position contradicts is refused, as Dedukti does). */
static tr_term obl_var_g, obl_var_arg, obl_var_have, obl_var_want;
static bool cst_headed(tr_term t, tr_occ *o) {
  uint32_t k;
  *o = head_of(t);
  return *o && is_cst(A_(*o, 1), &k);
}

/* pin(g, lhs, N) for v = var(N) of type x in g (fact otv): the first position of v in lhs (through
 * applications only: outside binders and brackets) as the argument of a constant-headed function
 * whose domain is convertible, under g, to x; or 0. */
static tr_occ pin_walk(tr_term g, tr_term t, tr_occ osub, tr_term v, tr_occ otv, tr_term x) {
  if (!is_app(t)) return 0;
  tr_term f = arg(t, 0), u = arg(t, 1), p, w;
  tr_occ ohf, otf;
  if (u == v && cst_headed(f, &ohf) && (otf = infer(g, f, &p)) != 0) {
    tr_occ ow = whnf_pos(p, &w), ocx;
    if (is_pi(w) && (ocx = cv_of(g, x, arg(w, 0))) != 0) {
      tr_occ ocw = cv_conv(g, w == p ? fire(&R_cv_refl, NULL, &p) : fire2(&R_cv_redl, ow, fire(&R_cv_refl, NULL, &w), NULL));
      tr_occ os[6] = {osub, ohf, otf, ocw, otv, ocx};
      tr_occ o = ocw ? fire(&R_pin, os, NULL) : 0;
      if (o) return o;
    }
  }
  tr_occ r = pin_walk(g, f, fire1(&R_sub_fun, osub, NULL), v, otv, x);
  return r ? r : pin_walk(g, u, fire1(&R_sub_arg, osub, NULL), v, otv, x);
}
/* obchk(g, u, a, X, Y) for u, abstractions over a constant-headed body, checked against a: the
 * body's type is not convertible to the expected codomain under g's hypotheses; or 0. */
static tr_occ obchk_of(tr_term g, tr_term u, tr_term a) {
  deep();
  if (is_lam(u)) {
    tr_term w;
    tr_occ ow = whnf_pos(a, &w);
    if (!is_pi(w)) return 0;
    tr_term g2 = CONS(arg(w, 0), g);
    if (!ctx_of(g2)) return 0;
    tr_occ inner = obchk_of(g2, arg(u, 1), arg(w, 1));
    if (!inner) return 0;
    tr_occ ocw = cv_conv(g, w == a ? fire(&R_cv_refl, NULL, &a) : fire2(&R_cv_redl, ow, fire(&R_cv_refl, NULL, &w), NULL));
    tr_term n = arg(u, 0);
    return fire2(&R_obchk_lam, ocw, inner, &n);
  }
  tr_occ oh;
  tr_term t;
  if (!cst_headed(u, &oh)) return 0;
  tr_occ ot = infer(g, u, &t);
  if (!ot || cv_of(g, t, a)) return 0;
  return fire2(&R_obchk_cst, ot, oh, &a);
}

static tr_occ obl_walk(tr_term g, tr_term lhs, tr_term t, tr_occ osub, bool *blocked) {
  if (!is_app(t) || *blocked) return 0;
  tr_term f = arg(t, 0), u = arg(t, 1), p, w, x;
  tr_occ r = obl_walk(g, lhs, f, fire1(&R_sub_fun, osub, NULL), blocked);
  if (r || *blocked) return r;
  r = obl_walk(g, lhs, u, fire1(&R_sub_arg, osub, NULL), blocked);
  if (r || *blocked) return r;
  tr_occ otf = infer(g, f, &p);
  if (!otf) return *blocked = true, 0;
  tr_occ ow = whnf_pos(p, &w);
  if (!is_pi(w)) return *blocked = true, 0;
  tr_occ ohf;
  bool fcst = cst_headed(f, &ohf);
  if (is_lam(u)) { /* a pattern abstraction is checked against F's domain pi(D, C) */
    tr_occ c;
    if (check(g, u, arg(w, 0), &c)) return 0;
    if (!fcst) return *blocked = true, 0;
    tr_term dw;
    whnf_pos(arg(w, 0), &dw);
    if (!is_pi(dw)) return *blocked = true, 0;
    tr_term d = arg(dw, 0), cc = arg(dw, 1), body = arg(u, 1), g2 = CONS(d, g), bt;
    /* cv(g, P, pi(pi(D, C), E)): F's domain must be the product as it stands */
    if (arg(w, 0) != dw) return *blocked = true, 0;
    tr_occ ocw = cv_conv(g, w == p ? fire(&R_cv_refl, NULL, &p) : fire2(&R_cv_redl, ow, fire(&R_cv_refl, NULL, &w), NULL));
    if (!ctx_of(g2)) return *blocked = true, 0;
    tr_occ ob = is_lam(body) ? 0 : infer(g2, body, &bt);
    if (ob && !cv_of(g2, bt, cc)) { /* the body's type is not the codomain: an obligation */
      tr_occ ohb;
      if (!cst_headed(body, &ohb)) return *blocked = true, 0;
      tr_occ o6[6] = {osub, otf, ocw, ob, ohf, ohb};
      return fire(&R_oblig_lamty, o6, NULL);
    }
    if (ob) return 0;
    if (is_lam(body)) { /* nested abstractions: the innermost body's type against its codomain */
      tr_occ oc = obchk_of(g, u, arg(w, 0));
      if (oc) {
        tr_occ o5[5] = {osub, otf, ocw, ohf, oc};
        tr_occ o = fire(&R_oblig_chk, o5, NULL);
        if (o) return o;
      }
    }
    /* an obligation inside the body, abstracted */
    bool inner_blocked = false;
    tr_occ oi = obl_walk(g2, body, body, fire(&R_sub_refl, NULL, &body), &inner_blocked);
    if (!oi) return *blocked = true, 0;
    tr_occ o5[5] = {osub, otf, ocw, oi, ohf};
    return fire(&R_oblig_lam, o5, NULL);
  }
  tr_occ otu = infer(g, u, &x);
  if (!otu) return *blocked = true, 0;
  if (cv_of(g, x, arg(w, 0))) return 0;
  tr_occ ohu;
  if (!fcst || !cst_headed(u, &ohu)) {
    uint32_t vn;
    if (fcst && is_var(u, &vn)) { /* a variable whose type another position pins: an obligation */
      tr_occ opin = pin_walk(g, lhs, fire(&R_sub_refl, NULL, &lhs), u, otu, x);
      tr_occ ocw = opin ? cv_conv(g, w == p ? fire(&R_cv_refl, NULL, &p) : fire2(&R_cv_redl, ow, fire(&R_cv_refl, NULL, &w), NULL)) : 0;
      if (ocw) {
        tr_occ os[6] = {osub, ohf, otf, ocw, otu, opin};
        tr_occ o = fire(&R_oblig_var, os, NULL);
        if (o) return o;
      }
    }
    obl_var_g = g, obl_var_arg = u, obl_var_have = x, obl_var_want = arg(w, 0);
    return *blocked = true, 0;
  }
  tr_occ ocw = cv_conv(g, w == p ? fire(&R_cv_refl, NULL, &p) : fire2(&R_cv_redl, ow, fire(&R_cv_refl, NULL, &w), NULL));
  tr_occ os[6] = {osub, otf, ocw, otu, ohf, ohu};
  return fire(&R_oblig, os, NULL);
}
static tr_occ find_obligation(tr_term g, tr_term lhs) {
  bool blocked = false;
  obl_var_g = obl_var_arg = obl_var_have = obl_var_want = TR_NONE;
  return obl_walk(g, lhs, lhs, fire(&R_sub_refl, NULL, &lhs), &blocked);
}

/* The first application subterm t of the left-hand side (outside binders, osub = sub(lhs, t))
 * that mentions only the context's first variables (indices >= cut at the whole context's scope)
 * and has an obligation in g, the context of those variables: the oblig fact, t, its sub fact,
 * and t at g's scope. */
static tr_occ prefix_obligation(tr_term g, tr_term t, tr_occ osub, uint32_t cut, tr_term *full, tr_occ *osubout,
                                tr_term *sp) {
  if (!is_app(t)) return 0;
  uint8_t *mk = xr(NULL, cut + 1);
  memset(mk, 0, cut + 1);
  fv_mark(t, 0, mk, cut);
  bool later = false;
  for (uint32_t i = 0; i < cut; i++) later |= mk[i] != 0;
  free(mk);
  if (!later) {
    tr_term s;
    if (!bl_ev(B, t, bl_rho(B, cut, NULL, 0), &s)) return 0;
    tr_occ o = find_obligation(g, s);
    if (o) *full = t, *osubout = osub, *sp = s;
    return o;
  }
  tr_occ o = prefix_obligation(g, arg(t, 0), fire1(&R_sub_fun, osub, NULL), cut, full, osubout, sp);
  return o ? o : prefix_obligation(g, arg(t, 1), fire1(&R_sub_arg, osub, NULL), cut, full, osubout, sp);
}

/* The shape of a pattern, checked before anything is typed (Dedukti refuses these on reading):
 * a pattern variable is applied to distinct variables bound by the pattern, and every other
 * application is headed by a constant or a bound variable (no redex, no product, no sort). */
static void check_pattern(tr_term t, uint32_t depth) {
  deep();
  if (head_sym(t) == f_brk) return;
  if (is_lam(t)) {
    check_pattern(arg(t, 1), depth + 1);
    return;
  }
  uint32_t na, k;
  tr_term h = spine(t, &na);
  if (is_var(h, &k) && k >= depth) {
    for (uint32_t j = 0; j < na; j++) {
      uint32_t y, y2;
      if (!is_var(spine_arg(t, na, j), &y) || y >= depth)
        refuse(BY_READER, "a pattern variable applied to something other than a bound variable (not a Miller pattern)");
      for (uint32_t i = 0; i < j; i++)
        if (is_var(spine_arg(t, na, i), &y2) && y2 == y)
          refuse(BY_READER, "a pattern variable applied twice to one bound variable (not a Miller pattern)");
    }
    return;
  }
  if (!is_var(h, &k) && !is_cst(h, &k) && head_sym(h) != f_brk) refuse(BY_READER, "this is not a pattern");
  for (uint32_t j = 0; j < na; j++) check_pattern(spine_arg(t, na, j), depth);
}

static bool applied_bracket(tr_term t) {
  if (is_app(t)) {
    uint32_t n;
    if (head_sym(spine(t, &n)) == f_brk) return true;
    return applied_bracket(arg(t, 0)) || applied_bracket(arg(t, 1));
  }
  if (is_lam(t)) return applied_bracket(arg(t, 1));
  return false;
}

/* mark[i] for each free var(i), i < m, of t under `depth` binders, outside brackets. */
static void mark_outside_brackets(tr_term t, uint32_t depth, uint8_t *mark, uint32_t m) {
  uint32_t k;
  if (head_sym(t) == f_brk) return;
  if (is_var(t, &k)) {
    if (k >= depth && k - depth < m) mark[k - depth] = 1;
  } else if (is_app(t)) {
    mark_outside_brackets(arg(t, 0), depth, mark, m);
    mark_outside_brackets(arg(t, 1), depth, mark, m);
  } else if (is_lam(t) || is_pi(t)) {
    mark_outside_brackets(arg(t, 0), depth, mark, m);
    mark_outside_brackets(arg(t, 1), depth + 1, mark, m);
  }
}

/* mark[i] for each free var(i), i < m, of t under `depth` binders (a C summary: it only chooses
 * the order of the context; the context's firings decide). */
static void fv_mark(tr_term t, uint32_t depth, uint8_t *mark, uint32_t m) {
  uint32_t k;
  if (bl_free_bound(B, t) <= depth) return;
  if (is_var(t, &k)) {
    if (k >= depth && k - depth < m) mark[k - depth] = 1;
  } else if (is_app(t)) {
    fv_mark(arg(t, 0), depth, mark, m);
    fv_mark(arg(t, 1), depth, mark, m);
  } else if (is_lam(t) || is_pi(t)) {
    fv_mark(arg(t, 0), depth, mark, m);
    fv_mark(arg(t, 1), depth + 1, mark, m);
  }
}

static void read_rule(uint32_t at_line) {
  /* [ context ] lhs --> rhs */
  cur_line = at_line;
  scope sc = {0};
  pvdecl *pd = NULL;
  uint32_t npd = 0, cappd = 0;
  expect(K_LSQ, "'['");
  while (tk.kind != K_RSQ) {
    if (tk.kind != K_ID) cur_line = tk.line, refuse(BY_READER, "expected a pattern variable");
    GROW(pd, npd, cappd);
    pd[npd].name = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
    pd[npd].type = TR_NONE;
    next();
    if (tk.kind == K_COLON) {
      next();
      sc.npv = npd; /* the type sees the earlier pattern variables */
      sc.pvars = xr(sc.pvars, (npd + 1) * sizeof *sc.pvars);
      for (uint32_t i = 0; i < npd; i++) sc.pvars[i] = pd[i].name;
      sc.cappv = npd + 1;
      pd[npd].type = pterm(&sc);
    }
    npd++;
    if (tk.kind == K_COMMA) next();
    else if (tk.kind != K_RSQ) cur_line = tk.line, refuse(BY_READER, "expected ',' or ']'");
  }
  next();
  sc.pvars = xr(sc.pvars, (npd + 1) * sizeof *sc.pvars);
  sc.cappv = npd + 1;
  sc.npv = npd;
  for (uint32_t i = 0; i < npd; i++) sc.pvars[i] = pd[i].name;
  sc.in_pattern = true;
  tr_term lhs0 = pterm(&sc);
  sc.in_pattern = false;
  expect(K_LONG, "'-->'");
  tr_term rhs0 = pterm(&sc);
  uint32_t m = sc.npv; /* named, then wildcards */
  tr_term lhs = to_delta(lhs0, m, 0), rhs = to_delta(rhs0, m, 0);
  uint32_t na, k;
  tr_term h = spine(lhs, &na);
  if (!is_cst(h, &k)) refuse(BY_READER, "the head of a left-hand side is not a constant");
  /* The context delta: each variable's type, given (moved to the whole of delta) or proposed from
   * the left-hand side; then an order of delta in which each type mentions only earlier
   * variables (the order is the checker's choice: the context's firings decide it is a context). */
  pvtype = xr(NULL, (m + 1) * sizeof *pvtype);
  for (uint32_t v = 0; v < m; v++) pvtype[v] = TR_NONE;
  nbv = 0;
  if (applied_bracket(lhs)) refuse(BY_READER, "a bracket applied to arguments");
  for (uint32_t j = 0; j < na; j++) check_pattern(spine_arg(lhs, na, j), 0);
  { /* every pattern variable occurs outside brackets (Dedukti: a bracket binds nothing) */
    uint8_t *seen = xr(NULL, m + 1);
    memset(seen, 0, m + 1);
    mark_outside_brackets(lhs, 0, seen, m);
    for (uint32_t v = 0; v < m; v++)
      if (!seen[m - 1 - v]) refuse(BY_READER, "pattern variable %s does not occur outside brackets", sc.pvars[v] ? sc.pvars[v] : "_");
    free(seen);
  }
  walk_pattern(lhs, TR_NONE, 0, m);
  tr_term *full = xr(NULL, (m + 1) * sizeof *full);
  bool proposed = false;
  const char **pvn = xr(NULL, (m + 1) * sizeof *pvn);
  tr_term *annfull = xr(NULL, (m + 1) * sizeof *annfull); /* an annotation checked afterwards */
  for (uint32_t v = 0; v < m; v++) {
    const char *name = sc.pvars[v] ? sc.pvars[v] : "_";
    annfull[v] = TR_NONE;
    if (v < npd && pd[v].type != TR_NONE) {
      if (!bl_ev(B, to_delta(pd[v].type, v, 0), bl_shk(B, m - v), &full[v])) noverdict("internal: a given type");
      if (pvtype[v] != TR_NONE) { /* Dedukti: the annotation must agree with the position's type */
        annfull[v] = full[v];
        full[v] = pvtype[v];
      }
    } else {
      proposed = true;
      if (pvtype[v] == TR_NONE) noverdict("no type could be proposed for pattern variable %s", name);
      full[v] = pvtype[v];
    }
  }
  uint8_t *deps = xr(NULL, (size_t)m * m + 1);
  memset(deps, 0, (size_t)m * m + 1);
  for (uint32_t v = 0; v < m; v++) fv_mark(full[v], 0, deps + (size_t)v * m, m);
  uint32_t *pos = xr(NULL, (m + 1) * sizeof *pos);
  bool *placed = xr(NULL, m + 1);
  memset(placed, 0, m + 1);
  /* the first variable, in reading order, whose type is ready; variables of closed types first, so
   * that obligations among earlier variables can be found before the types that need them */
  for (uint32_t p = 0; p < m; p++) {
    uint32_t pick = m;
    for (int closed_only = 1; closed_only >= 0 && pick == m; closed_only--)
      for (uint32_t v = 0; v < m && pick == m; v++) {
        if (placed[v]) continue;
        bool ready = true, closed = true;
        for (uint32_t j = 0; j < m; j++) /* var(m-1-j) is X_j */
          if (deps[(size_t)v * m + (m - 1 - j)]) {
            closed = false;
            if (!placed[j]) ready = false;
          }
        if (ready && (closed || !closed_only)) pick = v;
      }
    if (pick == m && getenv("DK_REF_TRACE"))
      for (uint32_t v = 0; v < m; v++) {
        fprintf(stderr, "dk_ref: pattern variable %s (%s): ", sc.pvars[v] ? sc.pvars[v] : "_", placed[v] ? "placed" : "waiting");
        print_term(stderr, full[v], 0);
        fputc('\n', stderr);
      }
    if (pick == m) noverdict("the pattern variables' types depend on each other in a cycle");
    placed[pick] = true;
    pos[pick] = p;
  }
  tr_term ren = bl_shk(B, 0); /* var(m-1-v) -> var(m-1-pos[v]) */
  for (uint32_t i = m; i-- > 0;) ren = bl_cs(B, VAR(m - 1 - pos[m - 1 - i]), ren);
  if (!bl_ev(B, lhs, ren, &lhs) || !bl_ev(B, rhs, ren, &rhs)) noverdict("internal: renaming delta");
  tr_term *ordered = xr(NULL, (m + 1) * sizeof *ordered);
  bool *annotated = xr(NULL, m + 1); /* by position in delta: the type in delta is the annotation */
  tr_term *annord = xr(NULL, (m + 1) * sizeof *annord); /* an annotation to check, by position */
  for (uint32_t v = 0; v < m; v++) {
    if (!bl_ev(B, full[v], ren, &ordered[pos[v]])) noverdict("internal: renaming a type");
    pvn[pos[v]] = sc.pvars[v] ? sc.pvars[v] : "_";
    annotated[pos[v]] = v < npd && pd[v].type != TR_NONE && annfull[v] == TR_NONE;
    annord[pos[v]] = TR_NONE;
    if (annfull[v] != TR_NONE && !bl_ev(B, annfull[v], ren, &annord[pos[v]])) noverdict("internal: renaming an annotation");
  }
  free(annfull);
  /* The context, entry by entry.  A proposed type may be well formed only under an obligation
   * among the earlier variables (an argument conversion in a subterm S of the left-hand side that
   * mentions only them): that hypothesis goes into the context before the entry, with its fact
   * oblig(G, S, X, A), and S is tied to the left-hand side by sub and a weakening ev fact. */
  tr_term lhs_ob = lhs, delta = NIL; /* obligations are searched outside brackets: a bracket's instance need not be typable */
  enum { IL_MAX = 32 };
  tr_term il_g[IL_MAX]; /* the context below each hypothesis inside the context; its justification: */
  tr_occ il_obl[IL_MAX], il_sub[IL_MAX], il_ev[IL_MAX];
  uint32_t nil = 0;
  for (uint32_t p = 0; p < m; p++) {
    tr_term tv, sort;
    if (!bl_ev(B, ordered[p], bl_rho(B, m - p, NULL, 0), &tv)) noverdict("internal: a type of delta mentions a later variable");
    while (proposed && !tys_of(delta, tv, true, &sort)) {
      if (nil == IL_MAX) noverdict("more than %d typing constraints inside the context", IL_MAX);
      tr_term sfull, sp;
      tr_occ osub, o = prefix_obligation(delta, lhs_ob, fire(&R_sub_refl, NULL, &lhs_ob), m - p, &sfull, &osub, &sp);
      if (!o) break; /* the context's firing will tell (no verdict below) */
      bool again = false;
      for (uint32_t i = 0; i < nil; i++) again |= A_(il_obl[i], 2) == A_(o, 2) && A_(il_obl[i], 3) == A_(o, 3);
      if (again) break;
      tr_term w;
      il_ev[nil] = bl_ev(B, sp, bl_shk(B, m - p), &w);
      if (!il_ev[nil] || w != sfull) noverdict("internal: weakening a subterm");
      il_g[nil] = delta, il_obl[nil] = o, il_sub[nil] = osub;
      nil++;
      delta = T3(f_hyp, A_(o, 2), A_(o, 3), delta);
      if (getenv("DK_REF_TRACE")) {
        fprintf(stderr, "dk_ref: typing hypothesis inside the context, before entry %u: ", p);
        print_term(stderr, A_(o, 2), 0), fputs(" == ", stderr), print_term(stderr, A_(o, 3), 0), fputc('\n', stderr);
      }
    }
    delta = CONS(tv, delta);
  }
  free(full), free(deps), free(pos), free(placed);
  /* the pattern */
  GROW(RR, nrr, caprr);
  rrule *R = &RR[nrr];
  memset(R, 0, sizeof *R);
  R->id = nrr;
  R->sym = k;
  R->k = na;
  R->m = m;
  R->lhs = lhs, R->rhs = rhs;
  char *nm = xr(NULL, strlen(SY[k].name) + 32);
  sprintf(nm, "rule %u of %s", (unsigned)SY[k].nrl + 1, SY[k].name);
  R->name = nm;
  R->top = xr(NULL, (na + 1) * sizeof *R->top);
  for (uint32_t j = 0; j < na; j++) R->top[j] = add_node(R, spine_arg(lhs, na, j), -1, 0, m);
  R->first_of_pv = xr(NULL, (m + 1) * sizeof *R->first_of_pv);
  for (uint32_t v = 0; v < m; v++) R->first_of_pv[v] = -1;
  for (uint32_t i = 0; i < R->nnodes; i++) {
    pnode *n = &R->nodes[i];
    if (n->kind != N_PVAR) continue;
    if (R->first_of_pv[n->pv] < 0) R->first_of_pv[n->pv] = (int)i;
    n->first = R->first_of_pv[n->pv];
    if (n->first != (int)i && R->nodes[n->first].a != n->a)
      refuse(BY_READER, "a repeated pattern variable with different arities");
    if (n->first != (int)i && LL) refuse(BY_READER, "a non-left-linear rule under --ll");
  }
  for (uint32_t v = 0; v < m; v++)
    if (R->first_of_pv[v] < 0) refuse(BY_READER, "pattern variable %s does not occur in the left-hand side", pvn[v]);
  R->delta = delta;
  /* admission: ctx(delta), ty(delta, lhs, T), ty(delta, rhs, T'), conv(T', T) */
  check_fail_have = check_fail_want = check_fail_g = TR_NONE;
  tr_occ octx = ctx_of(delta);
  if (!octx && getenv("DK_REF_TRACE"))
    for (tr_term d = delta; d != NIL; d = arg(d, 1)) {
      fprintf(stderr, "dk_ref: delta entry %s: ", ctx_of(d) ? "ok" : "NOT WELL FORMED");
      print_term(stderr, arg(d, 0), 0);
      fputc('\n', stderr);
    }
  if (!octx && proposed) noverdict("the types proposed for the pattern variables are not well formed");
  if (!octx) refuse_mismatch("the types of the pattern variables are not well formed");
  /* Dedukti types a left-hand side modulo the conversions its typing requires: each failed
   * argument conversion at an application of the left-hand side becomes a hypothesis, admitted
   * only with its fact oblig (every typable instance satisfies it); the right-hand side is then
   * typed under the hypotheses.  Obligations under the pattern's binders are not hosted. */
  tr_term g = delta, tl;
  tr_occ obl[64];
  tr_term oblg[64];
  uint32_t nh = 0;
  tr_occ olhs;
  tr_term lhs_ty = strip_brk(lhs); /* the left-hand side as a term to type: brackets as their terms */
  while (!(olhs = infer(g, lhs_ty, &tl))) {
    if (nh == 64) noverdict("more than 64 typing constraints");
    tr_occ o = find_obligation(g, lhs);
    uint32_t vi;
    if (!o && obl_var_g == g && is_var(obl_var_arg, &vi) && vi < m && annotated[m - 1 - vi]) {
      /* the variable's type is the user's annotation, which an instance need not respect, so the
       * conversion is no obligation of the left-hand side; Dedukti refuses the annotation */
      tr_occ on = has_hyp(g) ? 0 : notconv_neg(obl_var_have, obl_var_want);
      if (on)
        refuse(BY_FACT, "a pattern variable's annotated type is not convertible to the type its position imposes "
                        "(notconv fact %llu)", (unsigned long long)on);
      noverdict("a pattern variable's annotated type differs from the type its position imposes");
    }
    if (!o && obl_var_g == g)
      noverdict("the left-hand side is typable only under a conversion between pattern variables' types, which "
                "this checker does not take as a hypothesis");
    if (!o) noverdict("the left-hand side is typable only under constraints this checker does not host (under binders)");
    for (uint32_t i = 0; i < nh; i++)
      if (A_(obl[i], 2) == A_(o, 2) && A_(obl[i], 3) == A_(o, 3)) {
        if (getenv("DK_REF_TRACE") && check_fail_have != TR_NONE) {
          fputs("dk_ref: the conversion not found: ", stderr), print_term(stderr, check_fail_have, 0);
          fputs(" == ", stderr), print_term(stderr, check_fail_want, 0), fputc('\n', stderr);
        }
        noverdict("a typing constraint the hypotheses do not discharge (the search under hypotheses is not complete)");
      }
    if (getenv("DK_REF_TRACE")) {
      fprintf(stderr, "dk_ref: typing hypothesis %u: ", nh);
      print_term(stderr, A_(o, 2), 0), fputs(" == ", stderr), print_term(stderr, A_(o, 3), 0), fputc('\n', stderr);
    }
    oblg[nh] = g;
    obl[nh++] = o;
    g = T3(f_hyp, A_(o, 2), A_(o, 3), g);
    if (!ctx_of(g)) noverdict("internal: a context with a hypothesis");
  }
  /* Typing constraints refuted by facts: nosol (no solution: the rule never fires on a typable
   * term) or nowf (no well-founded solution: it fires only on instances built from terms without a
   * normal form, which a non-terminating rule can make typable).  Either way the rule is sound: its
   * right-hand side is typed under hypotheses that every typable instance satisfies, and no firing
   * concludes anything from their having no (well-founded) solution.  --type-lhs, Dedukti's "forbid
   * rules with untypable left-hand side" (error 108), refuses it with its class; otherwise it is
   * admitted and reported. */
  tr_occ oref = has_hyp(g) ? refute_hyps(g) : 0;
  bool nowf = oref && head_sym(rk_label(&E, oref)) == f_nowf;
  const char *refvar = "?";
  uint32_t rv;
  if (nowf && is_var(A_(oref, 1), &rv) && rv < m) refvar = pvn[m - 1 - rv];
  if (oref && TYPE_LHS) {
    if (nowf)
      refuse(BY_FACT, "--type-lhs: the typing constraints have no well-founded solution: they equate pattern variable "
                      "%s with a term that contains it under static symbols and abstractions (nowf fact %llu)",
             refvar, (unsigned long long)oref);
    refuse(BY_FACT, "--type-lhs: the typing constraints have no solution, so no instance of the left-hand side is "
                    "typable (nosol fact %llu)", (unsigned long long)oref);
  }
  /* lie 4: the hypothesis "the right-hand side's type is the left-hand side's" on top of the
   * context, with nothing to justify it; everything is typed under it, and the justification
   * offered is the honest context's */
  tr_term lie_g = TR_NONE;
  if (LIE == 4) {
    tr_term t1, tl2;
    tr_occ ol;
    if (infer(g, rhs, &t1)) {
      tr_term gl = T3(f_hyp, t1, tl, g);
      if (ctx_of(gl) && (ol = infer(gl, lhs_ty, &tl2)) != 0) lie_g = g, g = gl, olhs = ol, tl = tl2;
    }
  }
  /* each annotation agrees, under the hypotheses, with the type its variable's position imposes */
  tr_occ *annocc = xr(NULL, (m + 1) * sizeof *annocc);
  for (uint32_t p = 0; p < m; p++) {
    annocc[p] = 0;
    if (annord[p] == TR_NONE) continue;
    annocc[p] = cv_of(g, annord[p], ordered[p]);
    if (annocc[p]) continue;
    tr_occ on = has_hyp(g) ? 0 : notconv_neg(annord[p], ordered[p]);
    if (on)
      refuse(BY_FACT, "the annotated type of pattern variable %s is not convertible to the type its position imposes "
                      "(notconv fact %llu)", pvn[p], (unsigned long long)on);
    noverdict("the annotated type of pattern variable %s was not shown to agree with its position", pvn[p]);
  }
  tr_occ ocv, orhs = check(g, rhs, tl, &ocv);
  if (!orhs) refuse_mismatch("the right-hand side does not have the type of the left-hand side");
  if (SY[k].kind != SK_DEFINABLE) refuse(BY_FIRING, "a rule for %s, which is not definable", SY[k].name);
  /* every hypothesis of the context is justified: just(lhs, 0, g), made by firings */
  hjust *hj = xr(NULL, (nh + nil + 1) * sizeof *hj);
  for (uint32_t i = 0; i < nh; i++) { /* on top of the context: obligations of the left-hand side itself */
    tr_term w;
    tr_occ oev = bl_ev(B, lhs, bl_shk(B, 0), &w);
    if (!oev || w != lhs) noverdict("internal: the left-hand side under shk(0)");
    hj[i] = (hjust){oblg[i], A_(obl[i], 2), A_(obl[i], 3), obl[i], fire(&R_sub_refl, NULL, &lhs), oev};
  }
  for (uint32_t i = 0; i < nil; i++) /* inside the context: obligations of subterms over earlier variables */
    hj[nh + i] = (hjust){il_g[i], A_(il_obl[i], 2), A_(il_obl[i], 3), il_obl[i], il_sub[i], il_ev[i]};
  tr_occ ojust = just_of(lhs, 0, lie_g != TR_NONE ? lie_g : g, hj, nh + nil);
  free(hj);
  if (!ojust) noverdict("internal: a hypothesis of the context without its justification");
  rk_rule r;
  rk_init(&r, "a rule admission", 4); /* T0 T'1 L2 E3 */
  rk_read(&r, T1(f_ctx, g));
  rk_read(&r, T3(f_just, lhs, ZERO, g));
  rk_read(&r, TY(g, lhs_ty, L(0)));
  rk_read(&r, TY(g, rhs, L(1)));
  rk_read(&r, T3(f_cv, g, L(1), L(0)));
  uint32_t nann = 0;
  for (uint32_t p = 0; p < m; p++)
    if (annocc[p]) rk_read(&r, T3(f_cv, g, annord[p], ordered[p])), nann++;
  rk_take(&r, T2(f_rules, tr_code(C, k), L(2)));
  rk_take(&r, T1(f_epoch, L(3)));
  r.fresh = 1;
  rk_make(&r, T2(f_rules, tr_code(C, k), CONS(T2(f_rl, tr_code(C, R->id), NAT(na)), L(2))));
  rk_make(&r, T1(f_epoch, tr_fresh(C, 0)));
  tr_occ *occs = xr(NULL, (7 + nann) * sizeof *occs), made[2];
  occs[0] = SY[k].rules, occs[1] = epoch_occ, occs[2] = ctx_of(g), occs[3] = ojust, occs[4] = olhs, occs[5] = orhs;
  occs[6] = ocv;
  uint32_t j = 7;
  for (uint32_t p = 0; p < m; p++)
    if (annocc[p]) occs[j++] = annocc[p];
  if (nil) n_hyp_rules += !nh;
  if (!rk_fire(&E, &r, occs, NULL, made, NULL)) {
    if (LIE) fprintf(stderr, "dk_ref: the step refused the admission of %s (a lie)\n", R->name);
    refuse(BY_FIRING, "the admission of %s", R->name);
  }
  free(occs);
  rk_free(&r);
  if (nh) n_hyp_rules++;
  SY[k].rules = made[0];
  epoch_occ = made[1];
  epoch_name = A_(made[1], 0);
  epoch_no++;
  install_firings(R);
  GROW(SY[k].rl, SY[k].nrl, SY[k].caprl);
  SY[k].rl[SY[k].nrl++] = R->id;
  nrr++;
  n_rules++;
  if (oref && !QUIET) {
    if (nowf)
      fprintf(stderr, "NOTE %s:%u: %s admitted; its typing constraints have no well-founded solution (pattern "
                      "variable %s; nowf fact %llu): it fires only on instances built from terms without a normal "
                      "form\n", cur_file, cur_line, R->name, refvar, (unsigned long long)oref);
    else
      fprintf(stderr, "NOTE %s:%u: %s admitted; its typing constraints have no solution (nosol fact %llu): it "
                      "never fires on a typable term\n", cur_file, cur_line, R->name, (unsigned long long)oref);
  }
  free(pvtype);
  free(annotated), free(annord), free(annocc), free(ordered), free(pvn);
  for (uint32_t i = 0; i < npd; i++) free(pd[i].name);
  free(pd);
  free(sc.pvars);
  free(sc.names);
}

/* ---- commands ---- */

static void eval_cmd(tr_term t, bool infer_only, long budget) {
  tr_term ty;
  check_fail_have = check_fail_want = check_fail_g = TR_NONE;
  if (!infer(NIL, t, &ty)) refuse_mismatch("an ill-typed term in a command");
  /* Computed even when not printed: Dedukti evaluates, may not terminate, and may meet a
   * bracket's guard that fails.  With a step budget ([n]) it stops after n head steps. */
  tr_term n = infer_only ? ty : t, next;
  if (budget < 0) snf_pos(n, &n);
  else
    for (long i = 0; i < budget && head_step(n, &next); i++) n = next;
  if (QUIET) return;
  print_term(stdout, n, 0);
  fputc('\n', stdout);
}

/* #ASSERT / #ASSERTNOT / #CHECK / #CHECKNOT, conversion or typing. */
static void assert_cmd(bool positive, bool fatal, tr_term a, tr_term b, bool typing) {
  /* Dedukti: t1 == t2 holds when both are typed, their types are convertible and they are; a
   * typing t : A holds when t checks against A.  Either outcome is decided by a firing: the
   * statement's facts, or a non-convertibility fact. */
  check_fail_have = check_fail_want = check_fail_g = TR_NONE;
  int holds = -1; /* 1 holds, 0 does not, -1 undecided */
  tr_occ occs[5];
  rk_rule r;
  rk_init(&r, "an assertion", 3); /* T0 T'1 E2 */
  rk_read(&r, TY(NIL, a, L(0)));
  if (typing) {
    tr_occ oc, oa = check(NIL, a, b, &oc);
    if (oa) {
      rk_read(&r, T3(f_cv, NIL, L(0), b));
      occs[0] = oa, occs[1] = oc, holds = 1;
    } else {
      tr_term ta;
      tr_occ oi = infer(NIL, a, &ta), on = oi ? notconv_neg(ta, b) : 0;
      if (on) {
        rk_read(&r, T3(f_notconv, L(0), b, L(2)));
        rk_read(&r, T1(f_epoch, L(2)));
        occs[0] = oi, occs[1] = on, occs[2] = epoch_occ, holds = 0;
      }
    }
  } else {
    tr_term ta, tb;
    tr_occ oa = infer(NIL, a, &ta);
    if (!oa) refuse_mismatch("an ill-typed term in an assertion");
    tr_occ ob = infer(NIL, b, &tb);
    if (!ob) refuse_mismatch("an ill-typed term in an assertion");
    rk_read(&r, TY(NIL, b, L(1)));
    occs[0] = oa, occs[1] = ob;
    tr_occ oct = conv_pos(ta, tb), oc = oct ? conv_pos(a, b) : 0;
    if (oc) {
      rk_read(&r, CONV(L(0), L(1)));
      rk_read(&r, CONV(a, b));
      occs[2] = oct, occs[3] = oc, holds = 1;
    } else {
      tr_occ on = oct ? notconv_neg(a, b) : notconv_neg(ta, tb);
      if (on) {
        rk_read(&r, oct ? T3(f_notconv, a, b, L(2)) : T3(f_notconv, L(0), L(1), L(2)));
        rk_read(&r, T1(f_epoch, L(2)));
        occs[2] = on, occs[3] = epoch_occ, holds = 0;
      }
    }
  }
  if (holds >= 0 && !rk_fire(&E, &r, occs, NULL, NULL, NULL)) refuse(BY_FIRING, "the assertion's firing");
  rk_free(&r);
  if (fatal) {
    if (holds < 0 && positive) refuse(BY_ORDER, "assertion: no derivation found");
    if (holds < 0) noverdict("negative assertion: neither the statement nor its failure was derived");
    if (holds != positive) refuse(BY_FACT, "%s failed: %s", positive ? "assertion" : "negative assertion",
                                  holds ? "the statement holds" : "a non-convertibility fact refutes it");
  } else if (!QUIET)
    puts(holds < 0 ? "UNDECIDED" : holds == positive ? "YES" : "NO");
  n_asserts++;
}

static tr_term read_closed_term(bool applicative) {
  scope sc = {0};
  tr_term t = applicative ? paterm(&sc) : pterm(&sc);
  free(sc.names);
  free(sc.pvars);
  return t;
}

/* params (x : A) ... before ':' or ':='. */
static void read_decl(int kind, uint32_t at_line) {
  cur_line = at_line;
  if (tk.kind != K_ID) cur_line = tk.line, refuse(BY_READER, "expected an identifier");
  char *id = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
  next();
  scope sc = {0};
  tr_term doms[256];
  uint32_t np = 0;
  while (tk.kind == K_LPAR) {
    next();
    if (tk.kind != K_ID) cur_line = tk.line, refuse(BY_READER, "expected a parameter");
    char *x = strcpy(xr(NULL, strlen(tk.text) + 1), tk.text);
    next();
    expect(K_COLON, "':'");
    if (np == 256) noverdict("more than 256 parameters");
    doms[np++] = pterm(&sc);
    expect(K_RPAR, "')'");
    push_name(&sc, x);
    free(x);
  }
  tr_term ty = TR_NONE, body = TR_NONE;
  if (tk.kind == K_COLON) next(), ty = pterm(&sc);
  if (tk.kind == K_DEFEQ) next(), body = pterm(&sc);
  cur_line = at_line;
  if (tk.kind != K_DOT) cur_line = tk.line, refuse(BY_READER, "expected '.'");
  if (ty == TR_NONE && body == TR_NONE) refuse(BY_READER, "a declaration without a type");
  if ((kind == SK_STATIC || kind == SK_DEFINABLE) && body != TR_NONE) refuse(BY_READER, "a body without 'def' or 'thm'");
  if (kind == SK_THM && body == TR_NONE) refuse(BY_READER, "a theorem without a body");
  for (uint32_t i = np; i-- > 0;) {
    if (ty != TR_NONE) ty = PI(doms[i], ty);
    if (body != TR_NONE) body = LAM(doms[i], body);
  }
  while (sc.n) pop_name(&sc);
  free(sc.names);
  if (kind == SK_DEFN && body == TR_NONE) kind = SK_DEFINABLE;
  declare(kind, id, ty, body);
  free(id);
  next(); /* the dot */
}

static void read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  cur_file = path;
  if (!f) {
    fprintf(stderr, "dk_ref: cannot open %s\n", path);
    exit(2);
  }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = xr(NULL, (size_t)sz + 1);
  if (sz < 0 || fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
    fprintf(stderr, "dk_ref: cannot read %s\n", path);
    exit(2);
  }
  fclose(f);
  buf[sz] = 0;
  /* the module: the file's base name without .dk */
  const char *base = strrchr(path, '/');
  base = base ? base + 1 : path;
  size_t bl = strlen(base);
  if (bl > 3 && !strcmp(base + bl - 3, ".dk")) bl -= 3;
  free(module_name);
  module_name = dupn(base, bl);
  src = buf, len = (size_t)sz, pos = 0, line = 1;
  tk.text = NULL;
  next();
  while (tk.kind != K_EOF) {
    uint32_t at = tk.line;
    cur_line = at;
    switch (tk.kind) {
    case K_DEF: next(); read_decl(SK_DEFN, at); break;
    case K_THM: next(); read_decl(SK_THM, at); break;
    case K_INJ: next(), decl_injective = true, read_decl(SK_DEFINABLE, at), decl_injective = false; break;
    case K_PRV:
      next();
      if (tk.kind == K_DEF) next(), read_decl(SK_DEFN, at);
      else if (tk.kind == K_INJ) next(), decl_injective = true, read_decl(SK_DEFINABLE, at), decl_injective = false;
      else if (tk.kind == K_DEFAC || tk.kind == K_DEFACU) noverdict("AC symbols (defac) are not hosted");
      else read_decl(SK_STATIC, at);
      break;
    case K_DEFAC:
    case K_DEFACU: noverdict("AC symbols (defac, defacu) are not hosted");
    case K_ID: read_decl(SK_STATIC, at); break;
    case K_LSQ:
    case K_LBRA:
      for (;;) {
        if (tk.kind == K_LBRA) { /* {name} */
          next();
          if (tk.kind != K_ID && tk.kind != K_QID) cur_line = tk.line, refuse(BY_READER, "expected a rule name");
          next();
          expect(K_RBRA, "'}'");
        }
        read_rule(tk.line);
        if (tk.kind == K_DOT) break;
        if (tk.kind != K_LSQ && tk.kind != K_LBRA) cur_line = tk.line, refuse(BY_READER, "expected '.' after the rules");
      }
      next();
      break;
    case K_EVAL:
    case K_INFER: {
      bool inf = tk.kind == K_INFER, steps = false;
      long budget = -1;
      next();
      if (tk.kind == K_LSQ) { /* a configuration: [SNF], [WHNF, 3] ... (it changes only what is printed) */
        bool target = false, strat = false;
        next();
        for (;;) {
          if (tk.kind != K_ID) cur_line = tk.line, refuse(BY_READER, "invalid command configuration");
          const char *s = tk.text;
          bool num = *s != 0;
          for (const char *p = s; *p; p++) num &= isdigit((unsigned char)*p) != 0;
          if ((!strcmp(s, "SNF") || !strcmp(s, "WHNF")) && !target) target = true;
          else if ((!strcmp(s, "CBN") || !strcmp(s, "CBV") || !strcmp(s, "CBSV")) && !strat) strat = true;
          else if (num && !steps) steps = true, budget = atol(s);
          else cur_line = tk.line, refuse(BY_READER, "invalid command configuration");
          next();
          if (tk.kind == K_COMMA) {
            next();
            continue;
          }
          break;
        }
        expect(K_RSQ, "']'");
      }
      tr_term t = read_closed_term(false);
      if (tk.kind != K_DOT) cur_line = tk.line, refuse(BY_READER, "expected '.'");
      eval_cmd(t, inf, budget);
      n_cmds++;
      next();
      break;
    }
    case K_CHECK:
    case K_CHECKNOT:
    case K_ASSERT:
    case K_ASSERTNOT: {
      int k = tk.kind;
      next();
      tr_term a = read_closed_term(true);
      bool typing = tk.kind == K_COLON;
      if (tk.kind != K_COLON && tk.kind != K_EQUAL) cur_line = tk.line, refuse(BY_READER, "expected ':' or '=='");
      next();
      tr_term b = read_closed_term(false);
      if (tk.kind != K_DOT) cur_line = tk.line, refuse(BY_READER, "expected '.'");
      cur_line = at;
      assert_cmd(k == K_CHECK || k == K_ASSERT, k == K_ASSERT || k == K_ASSERTNOT, a, b, typing);
      next();
      break;
    }
    case K_PRINT:
      next();
      if (tk.kind != K_STRING) cur_line = tk.line, refuse(BY_READER, "expected a string");
      if (!QUIET) puts(tk.text);
      next();
      expect(K_DOT, "'.'");
      break;
    case K_NAME:
    case K_GDT:
      next();
      if (tk.kind != K_ID && tk.kind != K_QID) cur_line = tk.line, refuse(BY_READER, "expected an identifier");
      next();
      expect(K_DOT, "'.'");
      break;
    case K_REQUIRE: {
      next();
      if (tk.kind != K_ID) cur_line = tk.line, refuse(BY_READER, "expected a module name");
      bool seen = false;
      const char *mname = tk.text;
      size_t n = strlen(mname);
      if (n >= 4 && !strncmp(mname, "{|", 2)) mname += 2, n -= 4; /* {|module|} */
      for (uint32_t i = 0; i < nsy && !seen; i++) seen = !strncmp(SY[i].name, mname, n) && SY[i].name[n] == '.';
      if (!seen && (strlen(module_name) != n || strncmp(mname, module_name, n)))
        noverdict("#REQUIRE of module %.*s, which this run has not checked", (int)n, mname);
      next();
      expect(K_DOT, "'.'");
      break;
    }
    case K_PRAGMA: next(); break;
    default: cur_line = tk.line; refuse(BY_READER, "unexpected token");
    }
  }
  free(buf);
  free(tk.text);
  tk.text = NULL;
}

/* ============================================================================================ */

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static const char *emit_path;
static int run(int argc, char **argv) {
  double t0 = now();
  int nfiles = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--coc")) COC = true;
    else if (!strcmp(argv[i], "--eta")) ETA = true;
    else if (!strcmp(argv[i], "--ll")) LL = true;
    else if (!strcmp(argv[i], "--standard")) continue;
    else if (!strcmp(argv[i], "--sr-check") && i + 1 < argc) i++;
    else if (!strncmp(argv[i], "--sr-check=", 11)) continue;
    else if (!strcmp(argv[i], "--type-lhs")) TYPE_LHS = true; /* refuses refuted typing constraints */
    else if (!strcmp(argv[i], "-q")) QUIET = true;
    else if (!strcmp(argv[i], "--stats")) STATS = true;
    else if (!strcmp(argv[i], "-I") && i + 1 < argc) i++;
    else if (!strcmp(argv[i], "--emit-tcs") && i + 1 < argc) emit_path = argv[++i];
    else if (argv[i][0] == '-') {
      fprintf(stderr, "dk_ref: unknown option %s\n", argv[i]);
      return 2;
    } else
      nfiles++;
  }
  if (!nfiles && !emit_path) {
    fprintf(stderr, "usage: %s [--coc] [--eta] [--type-lhs] [-q] [--stats] FILE.dk ...\n", argv[0]);
    return 2;
  }
  FAULT = getenv("DK_FAULT") ? atoi(getenv("DK_FAULT")) : 0;
  LIE = getenv("DK_LIE") ? atoi(getenv("DK_LIE")) : 0;
  if (getenv("BL_FAULT")) bl_fault = atoi(getenv("BL_FAULT"));
  C = tr_ctx_new();
  S = tr_state_new(C);
  rk_engine_init(&E, C, S);
  static const uint8_t b00[2] = {0, 0}, b01[2] = {0, 1}, bd[1] = {BL_DATA};
  /* brk(t) marks a bracket in a rule's pattern; it never occurs in a term that is typed */
  bl_con cons[] = {{"app", 2, b00}, {"lam", 2, b01}, {"pi", 2, b01}, {"cst", 1, bd},
                   {"type", 0, NULL}, {"kind", 0, NULL}, {"none", 0, NULL}, {"brk", 1, b00}};
  B = bl_new(&E, cons, sizeof cons / sizeof *cons);
  c_app = bl_symbol(B, 0), c_lam = bl_symbol(B, 1), c_pi = bl_symbol(B, 2), c_cst = bl_symbol(B, 3);
  c_type = bl_symbol(B, 4), c_kind = bl_symbol(B, 5), c_none = bl_symbol(B, 6);
  f_rd = tr_symbol(C, "rd", 2), f_conv = tr_symbol(C, "conv", 2), f_ctx = tr_symbol(C, "ctx", 1);
  f_nil = tr_symbol(C, "nil", 0), f_cons = tr_symbol(C, "cons", 2), f_lookup = tr_symbol(C, "lookup", 3);
  f_ty = tr_symbol(C, "ty", 3), f_tys = tr_symbol(C, "tys", 3), f_decl = tr_symbol(C, "decl", 2);
  f_static = tr_symbol(C, "static", 1), f_defn = tr_symbol(C, "defn", 2), f_rules = tr_symbol(C, "rules", 2);
  f_rl = tr_symbol(C, "rl", 2), f_epoch = tr_symbol(C, "epoch", 1), f_head = tr_symbol(C, "head", 3);
  f_hn = tr_symbol(C, "hn", 2), f_wh = tr_symbol(C, "wh", 3), f_nomatch = tr_symbol(C, "nomatch", 3);
  f_nmall = tr_symbol(C, "nmall", 4), f_lt = tr_symbol(C, "lt", 2), f_nf = tr_symbol(C, "nf", 3);
  f_nfw = tr_symbol(C, "nfw", 3), f_nc = tr_symbol(C, "nc", 3), f_notconv = tr_symbol(C, "notconv", 3);
  f_shape = tr_symbol(C, "shape", 2), f_sv = tr_symbol(C, "sv", 2), f_sc = tr_symbol(C, "sc", 2);
  f_sl = tr_symbol(C, "sl", 0), f_sp = tr_symbol(C, "sp", 0), f_st = tr_symbol(C, "st", 0);
  f_sk = tr_symbol(C, "sk", 0), f_sn = tr_symbol(C, "sn", 0), f_z = tr_symbol(C, "z", 0), f_s = tr_symbol(C, "s", 1);
  f_var = tr_symbol(C, "var", 1), f_pv = tr_symbol(C, "pv", 2);
  f_hyp = tr_symbol(C, "hyp", 3), f_cv = tr_symbol(C, "cv", 3), f_sub = tr_symbol(C, "sub", 2);
  f_oblig = tr_symbol(C, "oblig", 4), f_brk = tr_symbol(C, "brk", 1), f_inj = tr_symbol(C, "injective", 1);
  f_just = tr_symbol(C, "just", 3), f_shk = tr_symbol(C, "shk", 1); /* shk: the binder layer's shift by k */
  f_pin = tr_symbol(C, "pin", 3);
  f_rocc = tr_symbol(C, "rocc", 2), f_rshape = tr_symbol(C, "rshape", 2), f_nosol = tr_symbol(C, "nosol", 3);
  f_nowf = tr_symbol(C, "nowf", 3), f_obchk = tr_symbol(C, "obchk", 5);
  TYPE = T0(c_type), KIND = T0(c_kind), NONE = T0(c_none), NIL = T0(f_nil), ZERO = NAT(0), ID = bl_id(B), SH = bl_sh(B);
  SL = T0(f_sl);
  init_rules();
  if (emit_path) return emit_tcs(emit_path);
#ifdef DK_SPEC
  size_t compiled = spec_link();
  if (STATS) fprintf(stderr, "dk_ref: %zu fixed rules decided by the specializer's code\n", compiled);
#endif
  epoch_occ = fire(&R_epoch0, NULL, NULL);
  epoch_name = A_(epoch_occ, 0);
  sym_add("?.?"); /* code 0 is never a symbol */
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-I") || !strcmp(argv[i], "--emit-tcs")) {
      i++;
      continue;
    }
    if (argv[i][0] == '-') continue;
    read_file(argv[i]);
  }
  if (!QUIET || STATS)
    fprintf(stderr,
            "accepted%s%s: %u declarations, %u definitions, %u theorems, %u rules (%u under typing hypotheses), "
            "%u assertions, %u commands; %llu firings (%llu refused), %zu facts, %zu terms [%.3f s]; "
            "%llu decisions by compiled rules\n",
            COC ? " (--coc)" : "", ETA ? " (--eta)" : "", n_decls, n_defs, n_thms, n_rules, n_hyp_rules, n_asserts, n_cmds,
            (unsigned long long)E.fired, (unsigned long long)E.refused, tr_present_count(S), tr_ctx_terms(C), now() - t0,
            (unsigned long long)E.fast_decisions);
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
  stack_room = STACK_SIZE - ((size_t)8 << 20);
  if (!pthread_attr_init(&a) && !pthread_attr_setstacksize(&a, STACK_SIZE) && !pthread_create(&th, &a, run_job, &j)) {
    pthread_join(th, NULL);
    return j.rc;
  }
  struct rlimit rl;
  stack_room = getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur > ((rlim_t)2 << 20)
                   ? (size_t)rl.rlim_cur - ((size_t)1 << 20)
                   : (size_t)7 << 20;
  run_job(&j);
  return j.rc;
}
