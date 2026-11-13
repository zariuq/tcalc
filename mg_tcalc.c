/* Megalodon (Egal HoTTG, HF, Mizar, HOAS) Natural-Deduction proof-kernel & -sexprinfo verifier on tcalc.
   Trust Ledger (protected judgement spaces + named, ledgered SPACE_HELPER assumptions):
   - SPACE_SIG    = 0 (protected via tc_protect): signature declarations SIG_PRIM(idx, tp),
     SIG_TERM(name, tp), and KNOWN_THM(name, prop), populated by pre-seal primitives and
     declaration/admission rules R_DECL_PARAM, R_DECL_DEF, R_DECL_AXIOM, R_THM_IMPORT.
   - SPACE_THM    = 1 (protected via tc_protect): type well-formedness PLAIN_WF(depth, tp),
     term typing HAS_TYPE(depth, tpl, t, tp), propositionhood IS_PROP(depth, tpl, p), and
     natural-deduction proof judgments THM(ctx, prop) — populated 100% by firing tcalc rules!
   - SPACE_HELPER = 2 (named, ledgered C helpers):
     1. C_HELPER_CONV(a, b): beta-delta-eta conversion mg_conv(a, b).
     2. C_HELPER_LT / C_HELPER_TPL_LOOKUP / C_HELPER_TML_LOOKUP: de Bruijn context lookup & index bound.
     3. C_HELPER_TPL_SHIFT1 / C_HELPER_TML_SHIFT1: de Bruijn context +1 shift.
     4. C_HELPER_TP_INST0 / C_HELPER_TM_INST0 / C_HELPER_TINST0: de Bruijn index-0 instantiation. */
/* What the rules do NOT decide (trusted to this file's C, beyond the helper facts above):
   - The declared type of a parameter. R_DECL_PARAM keeps PLAIN_WF(lv, body_tp) and makes
     SIG_TERM(name, tp). Its holes for the name and for tp are inputs (.inputs = 0xC): no premise
     relates tp to (lv, body_tp). The host computes tp = wrap_poly_tp(body_tp, lv) and supplies it.
     So the kernel has checked that body_tp is well formed at lv levels, and it has NOT checked that
     the type recorded for the name is body_tp under lv quantifiers.
   - The body of a definition. R_DECL_DEF keeps HAS_TYPE(0, TpLNil, body, tp) and makes
     SIG_TERM(name, tp): the fact records the name and its type. The body lives in the host's table
     (syms[h].def) and is what delta-conversion unfolds; no fact of the store ties a name to its body.
   - One declaration for each name. A second PARAM, PRIM or DEF of a name is compared with the first
     in the host's table (syms[h].has_term, syms[h].tp, syms[h].def) and refused or counted as a
     repeat there. No rule asks that SIG_TERM(name, _) be absent: fired twice with two types, the
     declaration rules make two signature facts for one name.
   - Conversion and the other helper facts are posted by C (see SPACE_HELPER above): a rule that keeps
     HELPER_CONV(a, b) has checked that C said a and b convert, with the host's table of bodies.
   The repair belongs to the rebuild on the reference kernel: a derived relation WRAP(lv, body, tp)
   kept by R_DECL_PARAM in place of the input hole; the body recorded as a fact and read by
   conversion; and an absence of an earlier SIG_TERM(name, _), or a minted name, in each
   declaration rule. No exploit of the present state is known or claimed; this is a list of what a
   proof checked here rests on. */
#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 700
#include <ctype.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "tcalc.h"
#include "tc_stack_guard.h"
#ifdef TC_USE_CESTA_EXPORT
#include "cesta/tc_scanner.export.h"
void tc_scanner_failure(void) { abort(); }
static const char *g_sx_buf_end = NULL;
#endif

/* The largest value an integer atom of the input may have.  Every integer in a proof file is
 * an index or a count of something the file itself contains, so it cannot exceed the file's
 * size in bytes; an atom beyond that (or one that does not fit in 64 bits) is malformed.
 * Without this bound a large number wrapped around when it was narrowed to an index. */
static uint64_t g_sx_int_max = INT32_MAX;

/* The run cannot go on for want of memory: no verdict, which is not a refusal. */
static void *got(void *p, const char *what) {
  if (!p) {
    fprintf(stderr, "mg_tcalc: no verdict: out of memory (%s)\n", what);
    exit(TC_STACK_GUARD_EXIT);
  }
  return p;
}

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e3 + ts.tv_nsec * 1e-6;
}

enum { SPACE_SIG = 0, SPACE_THM = 1, SPACE_HELPER = 2 };
enum { PROF_EGAL = 0, PROF_HF = 1, PROF_MIZAR = 2, PROF_HOAS = 3 };
static bool g_allow_axioms = true;

static int S_INT, S_NAME, S_TP, S_TM, S_TPL, S_TML, S_CTX, S_SIG, S_HELPER, S_THM, S_HANDLE;
static int C_TP_PROP, C_TP_BASE, C_TP_VAR, C_TP_ARR, C_TP_ALL;
static int C_TM_DB, C_TM_NAME, C_TM_PRIM, C_TM_AP, C_TM_LAM;
static int C_TM_IMP, C_TM_ALL, C_TM_TAP, C_TM_TLAM, C_TM_TALL;
static int C_TPLN, C_TPLC, C_TMLN, C_TMLC, C_CTX;
static int C_PLAIN_WF, C_HAS_TYPE, C_IS_PROP, C_THM;
static int C_SIG_PRIM, C_SIG_TERM, C_KNOWN_THM;
static int C_HELPER_CONV, C_HELPER_LT, C_HELPER_TPL_LOOKUP, C_HELPER_TML_LOOKUP;
static int C_HELPER_TPL_SHIFT1, C_HELPER_TML_SHIFT1;
static int C_HELPER_TP_INST0, C_HELPER_TM_INST0, C_HELPER_TINST0;
static int C_HANDLE, C_SUB_MARK, C_SUB_HYP, C_SUB_AUTH;
static int C_ACT_REQ, C_ACT_COMMIT;

static int R_WF_PROP, R_WF_BASE, R_WF_VAR, R_WF_ARR;
static int R_TY_DB, R_TY_PRIM, R_TY_NAME, R_TY_AP, R_TY_TAP, R_TY_LAM, R_TY_TLAM, R_TY_IMP, R_TY_ALL;
static int R_PROP_BASE, R_PROP_TALL;
static int R_DECL_PARAM, R_DECL_DEF, R_DECL_AXIOM, R_THM_IMPORT;
static int R_HYP, R_KNOWN, R_TERM_APP, R_PROOF_APP;
static int R_TERM_LAM, R_PROOF_LAM, R_TYPE_APP, R_TYPE_LAM;
static int R_SUB_BIRTH, R_SUB_USE_HYP, R_ACT_GATE;

static Term T_TP_PROP, T_TP_SET, T_TPLN, T_TMLN, T_CTX_EMPTY;

/* ---- Interned names & declarations ---- */
typedef struct {
  char *text;
  char *thm_name;
  uint32_t len, hash;
  Term nterm;
  /* term namespace */
  bool has_term;
  bool is_param;
  bool unfolded;
  bool dk_emitted_tm;
  bool dk_emitted_kn;
  uint64_t term_seq;
  Term tp;
  Term def;        /* beta-eta normal form if defined, 0 if parameter */
  Occ  sig_occ;    /* SPACE_SIG occurrence for SIG_TERM(nterm, tp) */
  /* known namespace */
  bool has_known;
  Term prop;
  Occ  known_sig_occ; /* SPACE_SIG occurrence for KNOWN_THM(nterm, prop) */
  Occ  known_occ;     /* SPACE_THM occurrence for THM(T_CTX_EMPTY, prop) */
} MgSym;

static MgSym *syms;
static uint32_t nsyms, capsyms;
static uint32_t *sym_tab;
static size_t sym_tab_cap;
static uint64_t next_decl_seq = 1;

static uint32_t hash_bytes(const char *s, size_t n) {
#ifdef TC_USE_CESTA_EXPORT
  return tc_scanner_fnv1a32((cesta_read_bytes){ (const uint8_t *)s, n });
#else
  uint32_t h = 2166136261u;
  for (size_t i = 0; i < n; i++) {
    h ^= (uint8_t)s[i];
    h *= 16777619u;
  }
  return h ? h : 1u;
#endif
}

/* ---- Per-Term metadata cache (fv, ftv, plain, nf, shift1) ---- */
typedef struct {
  uint32_t fv;       /* 1 + max free DB index, 0 if closed */
  uint32_t ftv;      /* 1 + max free type-var index, 0 if closed */
  uint32_t uval;     /* integer value for S_INT or symbol id for S_NAME */
  Term     nf;       /* beta-eta normal form */
  Term     shift1;   /* shift(0, +1) */
  uint8_t  init;
  uint8_t  plain;    /* for types: 1 if no C_TP_ALL */
  uint8_t  has_name; /* for terms: 1 if contains C_TM_NAME */
} NodeMeta;

static NodeMeta *NMETA;
static size_t nmeta_cap;
static Term *int_terms;
static size_t int_terms_cap;

static inline NodeMeta *meta_of(Term t) {
  if ((size_t)t >= nmeta_cap) {
    size_t nc = nmeta_cap ? nmeta_cap * 2 : (1u << 20);
    while (nc <= (size_t)t) nc *= 2;
    NodeMeta *nm = got(realloc(NMETA, nc * sizeof(NodeMeta)), "term annotations");
    memset(nm + nmeta_cap, 0, (nc - nmeta_cap) * sizeof(NodeMeta));
    NMETA = nm;
    nmeta_cap = nc;
  }
  return &NMETA[t];
}

static uint32_t sym_intern_n(const char *s, size_t len) {
  uint32_t h = hash_bytes(s, len);
  if (sym_tab_cap) {
    size_t mask = sym_tab_cap - 1;
    for (size_t i = h & mask;; i = (i + 1) & mask) {
      uint32_t id = sym_tab[i];
      if (!id) break;
      if (syms[id].hash == h && syms[id].len == len &&
          memcmp(syms[id].text, s, len) == 0)
        return id;
    }
  }
  if (nsyms + 1 >= capsyms) {
    uint32_t nc = capsyms ? capsyms * 2 : 1024;
    syms = realloc(syms, (size_t)nc * sizeof(MgSym));
    capsyms = nc;
  }
  if ((size_t)(nsyms + 1) * 2 >= sym_tab_cap) {
    size_t nc = sym_tab_cap ? sym_tab_cap * 2 : 2048;
    sym_tab = calloc(nc, sizeof(uint32_t));
    sym_tab_cap = nc;
    size_t mask = nc - 1;
    for (uint32_t j = 1; j <= nsyms; j++) {
      size_t k = syms[j].hash & mask;
      while (sym_tab[k]) k = (k + 1) & mask;
      sym_tab[k] = j;
    }
  }
  uint32_t id = ++nsyms;
  MgSym *e = &syms[id];
  memset(e, 0, sizeof(*e));
  e->text = malloc(len + 1);
  memcpy(e->text, s, len);
  e->text[len] = '\0';
  e->len = (uint32_t)len;
  e->hash = h;
  e->nterm = tc_name((uint16_t)S_NAME, tc_fresh_name());
  meta_of(e->nterm)->uval = id;
  size_t mask = sym_tab_cap - 1;
  size_t slot = h & mask;
  while (sym_tab[slot]) slot = (slot + 1) & mask;
  sym_tab[slot] = id;
  return id;
}

static uint32_t sym_intern(const char *s) {
  return sym_intern_n(s, strlen(s));
}

/* ---- Term & Type constructors on tcalc ---- */
static inline Term mk_int(uint32_t n) {
  if ((size_t)n >= int_terms_cap) {
    size_t nc = int_terms_cap ? int_terms_cap * 2 : 1024;
    while (nc <= (size_t)n) nc *= 2;
    Term *it = got(realloc(int_terms, nc * sizeof(Term)), "integer terms");
    memset(it + int_terms_cap, 0, (nc - int_terms_cap) * sizeof(Term));
    int_terms = it;
    int_terms_cap = nc;
  }
  if (!int_terms[n]) {
    Term t = tc_name((uint16_t)S_INT, tc_fresh_name());
    meta_of(t)->uval = n;
    int_terms[n] = t;
  }
  return int_terms[n];
}
static inline uint32_t int_val(Term t) {
  return meta_of(t)->uval;
}

static Term mk_tp_prop(void) {
  NodeMeta *m = meta_of(T_TP_PROP);
  if (!m->init) { m->init = 1; m->plain = 1; m->ftv = 0; }
  return T_TP_PROP;
}
static Term mk_tp_base(uint32_t idx) {
  if (idx == 0 && T_TP_SET) return T_TP_SET;
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TP_BASE, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->plain = 1; m->ftv = 0; }
  return t;
}
static Term mk_tp_var(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TP_VAR, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) { m->init = 1; m->plain = 1; m->ftv = idx + 1u; }
  return t;
}
static Term mk_tp_arr(Term dom, Term cod) {
  Term a[2] = { dom, cod };
  Term t = tc_app(C_TP_ARR, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta md = *meta_of(dom), mc = *meta_of(cod);
    m = meta_of(t);
    m->init = 1;
    m->plain = (uint8_t)(md.plain & mc.plain);
    m->ftv = md.ftv > mc.ftv ? md.ftv : mc.ftv;
  }
  return t;
}
static Term mk_tp_all(Term body) {
  Term a[1] = { body };
  Term t = tc_app(C_TP_ALL, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->plain = 0;
    m->ftv = mb.ftv > 0 ? mb.ftv - 1u : 0u;
  }
  return t;
}

static inline bool tp_plain_wf(Term tp, uint32_t depth) {
  NodeMeta *m = meta_of(tp);
  return m->plain && m->ftv <= depth;
}

static Term mk_tm_db(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_DB, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    m->init = 1; m->fv = idx + 1u; m->ftv = 0; m->has_name = 0; m->nf = t;
  }
  return t;
}
static Term mk_tm_name(uint32_t sym_id) {
  Term a[1] = { syms[sym_id].nterm };
  Term t = tc_app(C_TM_NAME, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    m->init = 1; m->fv = 0; m->ftv = 0; m->has_name = 1; m->nf = t;
  }
  return t;
}
static Term mk_tm_prim(uint32_t idx) {
  Term a[1] = { mk_int(idx) };
  Term t = tc_app(C_TM_PRIM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    m->init = 1; m->fv = 0; m->ftv = 0; m->has_name = 0; m->nf = t;
  }
  return t;
}
static Term mk_tm_ap(Term f, Term x) {
  Term a[2] = { f, x };
  Term t = tc_app(C_TM_AP, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mf = *meta_of(f), mx = *meta_of(x);
    m = meta_of(t);
    m->init = 1;
    m->fv = mf.fv > mx.fv ? mf.fv : mx.fv;
    m->ftv = mf.ftv > mx.ftv ? mf.ftv : mx.ftv;
    m->has_name = (uint8_t)(mf.has_name | mx.has_name);
  }
  return t;
}
static Term mk_tm_imp(Term p, Term q) {
  Term a[2] = { p, q };
  Term t = tc_app(C_TM_IMP, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mp = *meta_of(p), mq = *meta_of(q);
    m = meta_of(t);
    m->init = 1;
    m->fv = mp.fv > mq.fv ? mp.fv : mq.fv;
    m->ftv = mp.ftv > mq.ftv ? mp.ftv : mq.ftv;
    m->has_name = (uint8_t)(mp.has_name | mq.has_name);
  }
  return t;
}
static Term mk_tm_lam(Term tp, Term body) {
  Term a[2] = { tp, body };
  Term t = tc_app(C_TM_LAM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mt = *meta_of(tp), mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv > 0 ? mb.fv - 1u : 0u;
    m->ftv = mt.ftv > mb.ftv ? mt.ftv : mb.ftv;
    m->has_name = mb.has_name;
  }
  return t;
}
static Term mk_tm_all(Term tp, Term body) {
  Term a[2] = { tp, body };
  Term t = tc_app(C_TM_ALL, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mt = *meta_of(tp), mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv > 0 ? mb.fv - 1u : 0u;
    m->ftv = mt.ftv > mb.ftv ? mt.ftv : mb.ftv;
    m->has_name = mb.has_name;
  }
  return t;
}
static Term mk_tm_tap(Term f, Term tp) {
  Term a[2] = { f, tp };
  Term t = tc_app(C_TM_TAP, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mf = *meta_of(f), mt = *meta_of(tp);
    m = meta_of(t);
    m->init = 1;
    m->fv = mf.fv;
    m->ftv = mf.ftv > mt.ftv ? mf.ftv : mt.ftv;
    m->has_name = mf.has_name;
  }
  return t;
}
static Term mk_tm_tlam(Term body) {
  Term a[1] = { body };
  Term t = tc_app(C_TM_TLAM, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv;
    m->ftv = mb.ftv > 0 ? mb.ftv - 1u : 0u;
    m->has_name = mb.has_name;
  }
  return t;
}
static Term mk_tm_tall(Term body) {
  Term a[1] = { body };
  Term t = tc_app(C_TM_TALL, a);
  NodeMeta *m = meta_of(t);
  if (!m->init) {
    NodeMeta mb = *meta_of(body);
    m = meta_of(t);
    m->init = 1;
    m->fv = mb.fv;
    m->ftv = mb.ftv > 0 ? mb.ftv - 1u : 0u;
    m->has_name = mb.has_name;
  }
  return t;
}

static Term mk_tplc(Term h, Term t) {
  Term a[2] = { h, t };
  return tc_app(C_TPLC, a);
}
static Term mk_tmlc(Term h, Term t) {
  Term a[2] = { h, t };
  return tc_app(C_TMLC, a);
}
static Term mk_ctx(uint32_t depth, Term tpl, Term tml) {
  if (depth == 0 && tpl == T_TPLN && tml == T_TMLN && T_CTX_EMPTY)
    return T_CTX_EMPTY;
  Term a[3] = { mk_int(depth), tpl, tml };
  return tc_app(C_CTX, a);
}

static void unpack_ctx(Term ctx, uint32_t *depth, Term *tpl, Term *tml) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(ctx, &k, &h, &ar, &a);
  Term d_t = a[0], tp_t = a[1], tm_t = a[2];
  *depth = int_val(d_t);
  *tpl = tp_t;
  *tml = tm_t;
}

static Term list_nth(Term l, int cons_con, uint32_t idx) {
  for (;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(l, &k, &h, &ar, &a);
    if ((int)h != cons_con) return 0;
    if (idx == 0) return a[0];
    l = a[1];
    idx--;
  }
}

/* ---- Direct-mapped operation cache ---- */
enum {
  OP_TP_SHIFT = 1, OP_TP_INST, OP_TM_SHIFT, OP_TM_TSHIFT,
  OP_TM_INST, OP_TM_TINST, OP_INFER, OP_WF, OP_PROP
};
typedef struct {
  Term a, b, res;
  Occ  occ;
  uint32_t param;
  int32_t amount;
  uint8_t op;
} OpSlot;
#define OP_CACHE_SIZE (1u << 17)
static OpSlot op_cache[OP_CACHE_SIZE];

static inline uint32_t op_slot_idx(uint8_t op, Term a, Term b, uint32_t p, int32_t amt) {
  uint64_t h = (uint64_t)a * 0x9e3779b97f4a7c15ULL ^
               (uint64_t)b * 0xc2b2ae3d27d4eb4fULL ^
               ((uint64_t)op << 52) ^ ((uint64_t)p << 18) ^ (uint32_t)amt;
  h ^= h >> 29;
  return (uint32_t)h & (OP_CACHE_SIZE - 1u);
}

static inline Term op_cache_get(uint8_t op, Term a, Term b, uint32_t p, int32_t amt) {
  OpSlot *s = &op_cache[op_slot_idx(op, a, b, p, amt)];
  if (s->op == op && s->a == a && s->b == b && s->param == p && s->amount == amt)
    return s->res;
  return 0;
}

static inline void op_cache_put(uint8_t op, Term a, Term b, uint32_t p, int32_t amt, Term res) {
  if (!res) return;
  OpSlot *s = &op_cache[op_slot_idx(op, a, b, p, amt)];
  *s = (OpSlot){ a, b, res, 0, p, amt, op };
}

static inline Occ op_cache_get_occ(uint8_t op, Term a, Term b, uint32_t p, Term *out_res) {
  OpSlot *s = &op_cache[op_slot_idx(op, a, b, p, 0)];
  if (s->op == op && s->a == a && s->b == b && s->param == p && s->amount == 0 && s->occ) {
    if (out_res) *out_res = s->res;
    return s->occ;
  }
  return 0;
}

static inline void op_cache_put_occ(uint8_t op, Term a, Term b, uint32_t p, Term res, Occ occ) {
  if (!occ) return;
  OpSlot *s = &op_cache[op_slot_idx(op, a, b, p, 0)];
  *s = (OpSlot){ a, b, res, occ, p, 0, op };
}

/* ---- Shifting & Instantiation ---- */
static Term tp_shift(Term tp, uint32_t cutoff, int32_t amount) {
  if (!tp || amount == 0 || meta_of(tp)->ftv <= cutoff) return tp;
  if (cutoff == 0 && amount == 1 && meta_of(tp)->shift1) return meta_of(tp)->shift1;
  Term hit = op_cache_get(OP_TP_SHIFT, tp, 0, cutoff, amount);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  Term r = tp;
  if ((int)h == C_TP_VAR) {
    uint32_t idx = int_val(a[0]);
    if (idx >= cutoff) r = mk_tp_var((uint32_t)((int32_t)idx + amount));
  } else if ((int)h == C_TP_ARR) {
    Term d = a[0], c = a[1];
    Term d2 = tp_shift(d, cutoff, amount);
    Term c2 = tp_shift(c, cutoff, amount);
    r = (d2 == d && c2 == c) ? tp : mk_tp_arr(d2, c2);
  } else if ((int)h == C_TP_ALL) {
    Term b = a[0];
    Term b2 = tp_shift(b, cutoff + 1u, amount);
    r = (b2 == b) ? tp : mk_tp_all(b2);
  }
  if (cutoff == 0 && amount == 1) meta_of(tp)->shift1 = r;
  else op_cache_put(OP_TP_SHIFT, tp, 0, cutoff, amount, r);
  return r;
}

static Term tp_instantiate(Term tp, uint32_t depth, Term sub) {
  if (!tp || !sub || meta_of(tp)->ftv <= depth) return tp;
  Term hit = op_cache_get(OP_TP_INST, tp, sub, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  Term r = tp;
  if ((int)h == C_TP_VAR) {
    uint32_t idx = int_val(a[0]);
    if (idx < depth) r = tp;
    else if (idx == depth) r = tp_shift(sub, 0, (int32_t)depth);
    else r = mk_tp_var(idx - 1u);
  } else if ((int)h == C_TP_ARR) {
    Term d = a[0], c = a[1];
    Term d2 = tp_instantiate(d, depth, sub);
    Term c2 = tp_instantiate(c, depth, sub);
    r = (d2 == d && c2 == c) ? tp : mk_tp_arr(d2, c2);
  } else if ((int)h == C_TP_ALL) {
    Term b = a[0];
    Term b2 = tp_instantiate(b, depth + 1u, sub);
    r = (b2 == b) ? tp : mk_tp_all(b2);
  }
  op_cache_put(OP_TP_INST, tp, sub, depth, 0, r);
  return r;
}

static Term tm_shift(Term m, uint32_t cutoff, int32_t amount) {
  if (!m || amount == 0 || meta_of(m)->fv <= cutoff) return m;
  if (cutoff == 0 && amount == 1 && meta_of(m)->shift1) return meta_of(m)->shift1;
  Term hit = op_cache_get(OP_TM_SHIFT, m, 0, cutoff, amount);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx >= cutoff) r = mk_tm_db((uint32_t)((int32_t)idx + amount));
  } else if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_shift(f, cutoff, amount);
    Term x2 = tm_shift(x, cutoff, amount);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term b2 = tm_shift(b, cutoff + 1u, amount);
    if (b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp, b2) : mk_tm_all(tp, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_shift(f, cutoff, amount);
    if (f2 != f) r = mk_tm_tap(f2, tp);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_shift(b, cutoff, amount);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  if (cutoff == 0 && amount == 1) meta_of(m)->shift1 = r;
  else op_cache_put(OP_TM_SHIFT, m, 0, cutoff, amount, r);
  return r;
}

static Term tm_tshift(Term m, uint32_t cutoff, int32_t amount) {
  if (!m || amount == 0 || meta_of(m)->ftv <= cutoff) return m;
  Term hit = op_cache_get(OP_TM_TSHIFT, m, 0, cutoff, amount);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_tshift(f, cutoff, amount);
    Term x2 = tm_tshift(x, cutoff, amount);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term tp2 = tp_shift(tp, cutoff, amount);
    Term b2 = tm_tshift(b, cutoff, amount);
    if (tp2 != tp || b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp2, b2) : mk_tm_all(tp2, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_tshift(f, cutoff, amount);
    Term tp2 = tp_shift(tp, cutoff, amount);
    if (f2 != f || tp2 != tp) r = mk_tm_tap(f2, tp2);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_tshift(b, cutoff + 1u, amount);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  op_cache_put(OP_TM_TSHIFT, m, 0, cutoff, amount, r);
  return r;
}

static Term tm_instantiate(Term m, uint32_t depth, Term sub) {
  if (!m || !sub || meta_of(m)->fv <= depth) return m;
  Term hit = op_cache_get(OP_TM_INST, m, sub, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx < depth) r = m;
    else if (idx == depth) r = tm_shift(sub, 0, (int32_t)depth);
    else r = mk_tm_db(idx - 1u);
  } else if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_instantiate(f, depth, sub);
    Term x2 = tm_instantiate(x, depth, sub);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term b2 = tm_instantiate(b, depth + 1u, sub);
    if (b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp, b2) : mk_tm_all(tp, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_instantiate(f, depth, sub);
    if (f2 != f) r = mk_tm_tap(f2, tp);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_instantiate(b, depth, sub);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  op_cache_put(OP_TM_INST, m, sub, depth, 0, r);
  return r;
}

static Term tm_tinstantiate(Term m, uint32_t depth, Term sub_tp) {
  if (!m || !sub_tp || meta_of(m)->ftv <= depth) return m;
  Term hit = op_cache_get(OP_TM_TINST, m, sub_tp, depth, 0);
  if (hit) return hit;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Term r = m;
  int hc = (int)h;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    Term f2 = tm_tinstantiate(f, depth, sub_tp);
    Term x2 = tm_tinstantiate(x, depth, sub_tp);
    if (f2 != f || x2 != x) r = hc == C_TM_AP ? mk_tm_ap(f2, x2) : mk_tm_imp(f2, x2);
  } else if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    Term tp2 = tp_instantiate(tp, depth, sub_tp);
    Term b2 = tm_tinstantiate(b, depth, sub_tp);
    if (tp2 != tp || b2 != b) r = hc == C_TM_LAM ? mk_tm_lam(tp2, b2) : mk_tm_all(tp2, b2);
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    Term f2 = tm_tinstantiate(f, depth, sub_tp);
    Term tp2 = tp_instantiate(tp, depth, sub_tp);
    if (f2 != f || tp2 != tp) r = mk_tm_tap(f2, tp2);
  } else if (hc == C_TM_TLAM || hc == C_TM_TALL) {
    Term b = a[0];
    Term b2 = tm_tinstantiate(b, depth + 1u, sub_tp);
    if (b2 != b) r = hc == C_TM_TLAM ? mk_tm_tlam(b2) : mk_tm_tall(b2);
  }
  op_cache_put(OP_TM_TINST, m, sub_tp, depth, 0, r);
  return r;
}

static Term tpl_shift1(Term l) {
  if (l == T_TPLN) return l;
  if (meta_of(l)->shift1) return meta_of(l)->shift1;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(l, &k, &h, &ar, &a);
  Term hd = a[0], tl = a[1];
  Term r = mk_tplc(tp_shift(hd, 0, 1), tpl_shift1(tl));
  meta_of(l)->shift1 = r;
  return r;
}

static Term tml_shift1(Term l) {
  if (l == T_TMLN) return l;
  if (meta_of(l)->shift1) return meta_of(l)->shift1;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(l, &k, &h, &ar, &a);
  Term hd = a[0], tl = a[1];
  Term r = mk_tmlc(tm_shift(hd, 0, 1), tml_shift1(tl));
  meta_of(l)->shift1 = r;
  return r;
}

static bool tm_free_db(Term m, uint32_t idx) {
  if (meta_of(m)->fv <= idx) return false;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_DB) return int_val(a[0]) == idx;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    return tm_free_db(f, idx) || tm_free_db(x, idx);
  }
  if (hc == C_TM_LAM || hc == C_TM_ALL) return tm_free_db(a[1], idx + 1u);
  if (hc == C_TM_TAP || hc == C_TM_TLAM || hc == C_TM_TALL) return tm_free_db(a[0], idx);
  return false;
}

static bool tp_free_tv(Term tp, uint32_t idx) {
  if (meta_of(tp)->ftv <= idx) return false;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TP_VAR) return int_val(a[0]) == idx;
  if (hc == C_TP_ARR) {
    Term d = a[0], c = a[1];
    return tp_free_tv(d, idx) || tp_free_tv(c, idx);
  }
  if (hc == C_TP_ALL) return tp_free_tv(a[0], idx + 1u);
  return false;
}

static bool tm_free_tv(Term m, uint32_t idx) {
  if (meta_of(m)->ftv <= idx) return false;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_AP || hc == C_TM_IMP) {
    Term f = a[0], x = a[1];
    return tm_free_tv(f, idx) || tm_free_tv(x, idx);
  }
  if (hc == C_TM_LAM || hc == C_TM_ALL) {
    Term tp = a[0], b = a[1];
    return tp_free_tv(tp, idx) || tm_free_tv(b, idx);
  }
  if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1];
    return tm_free_tv(f, idx) || tp_free_tv(tp, idx);
  }
  if (hc == C_TM_TLAM || hc == C_TM_TALL) return tm_free_tv(a[0], idx + 1u);
  return false;
}

/* ---- Beta-eta normal form (for DEF bodies) ---- */
static Term tm_nf(Term m) {
  if (!m) return 0;
  if (meta_of(m)->nf) return meta_of(m)->nf;
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  Term r = m;
  if (hc == C_TM_AP) {
    Term f0 = a[0], x0 = a[1];
    Term f = tm_nf(f0);
    Term x = tm_nf(x0);
    uint8_t fk; uint32_t fh; int far; const Term *fa;
    tc_node(f, &fk, &fh, &far, &fa);
    if ((int)fh == C_TM_LAM) {
      r = tm_nf(tm_instantiate(fa[1], 0, x));
    } else {
      r = (f == f0 && x == x0) ? m : mk_tm_ap(f, x);
    }
  } else if (hc == C_TM_LAM) {
    Term tp = a[0], b0 = a[1];
    Term b = tm_nf(b0);
    uint8_t bk; uint32_t bh; int bar; const Term *ba;
    tc_node(b, &bk, &bh, &bar, &ba);
    if ((int)bh == C_TM_AP) {
      Term bf = ba[0], bx = ba[1];
      uint8_t xk; uint32_t xh; int xar; const Term *xa;
      tc_node(bx, &xk, &xh, &xar, &xa);
      if ((int)xh == C_TM_DB && int_val(xa[0]) == 0 && !tm_free_db(bf, 0)) {
        r = tm_shift(bf, 0, -1);
      } else {
        r = (b == b0) ? m : mk_tm_lam(tp, b);
      }
    } else {
      r = (b == b0) ? m : mk_tm_lam(tp, b);
    }
  } else if (hc == C_TM_TAP) {
    Term f0 = a[0], tp = a[1];
    Term f = tm_nf(f0);
    uint8_t fk; uint32_t fh; int far; const Term *fa;
    tc_node(f, &fk, &fh, &far, &fa);
    if ((int)fh == C_TM_TLAM) {
      r = tm_nf(tm_tinstantiate(fa[0], 0, tp));
    } else {
      r = (f == f0) ? m : mk_tm_tap(f, tp);
    }
  } else if (hc == C_TM_TLAM) {
    Term b0 = a[0];
    Term b = tm_nf(b0);
    uint8_t bk; uint32_t bh; int bar; const Term *ba;
    tc_node(b, &bk, &bh, &bar, &ba);
    if ((int)bh == C_TM_TAP) {
      Term bf = ba[0], btp = ba[1];
      uint8_t tk; uint32_t th; int tar; const Term *ta;
      tc_node(btp, &tk, &th, &tar, &ta);
      if ((int)th == C_TP_VAR && int_val(ta[0]) == 0 && !tm_free_tv(bf, 0)) {
        r = tm_tshift(bf, 0, -1);
      } else {
        r = (b == b0) ? m : mk_tm_tlam(b);
      }
    } else {
      r = (b == b0) ? m : mk_tm_tlam(b);
    }
  } else if (hc == C_TM_IMP) {
    Term p0 = a[0], q0 = a[1];
    Term p = tm_nf(p0), q = tm_nf(q0);
    r = (p == p0 && q == q0) ? m : mk_tm_imp(p, q);
  } else if (hc == C_TM_ALL) {
    Term tp = a[0], b0 = a[1];
    Term b = tm_nf(b0);
    r = (b == b0) ? m : mk_tm_all(tp, b);
  } else if (hc == C_TM_TALL) {
    Term b0 = a[0];
    Term b = tm_nf(b0);
    r = (b == b0) ? m : mk_tm_tall(b);
  }
  meta_of(m)->nf = r;
  meta_of(r)->nf = r;
  return r;
}

/* ---- Profile primitive tables (Egal HoTTG, HF, Mizar, HOAS) ---- */
static Term prim_types[8];
static Occ  prim_sig_occs[8];
static uint32_t nprims;

static uint64_t stat_total_tc_fires;

static inline Occ commit_mg_step(int rule, const Occ *keep, const Term *inst) {
  TcPreparedStep step = { .rule = rule, .keep = keep, .inst = inst };
  TcAdmissionReceipt rec;
  if (!tc_commit_prepared(&step, &rec)) return 0;
  stat_total_tc_fires++;
  return rec.out;
}

static inline Occ commit_mg_step_extra(int rule, const Occ *keep, const Term *inst, Occ *extra0) {
  TcPreparedStep step = { .rule = rule, .keep = keep, .inst = inst };
  TcAdmissionReceipt rec;
  if (!tc_commit_prepared(&step, &rec)) return 0;
  stat_total_tc_fires++;
  if (extra0) *extra0 = rec.extra[0];
  return rec.out;
}

static const char *profile_label(int profile) {
  switch (profile) {
  case PROF_EGAL:  return "egal";
  case PROF_HF:    return "hf";
  case PROF_MIZAR: return "mizar";
  case PROF_HOAS:  return "hoas";
  default:         return "unknown";
  }
}

static void init_profile_prims(int profile) {
  memset(prim_types, 0, sizeof(prim_types));
  memset(prim_sig_occs, 0, sizeof(prim_sig_occs));
  T_TP_SET = mk_tp_base(0);
  Term set = T_TP_SET;
  Term prop = mk_tp_prop();
  Term set_set = mk_tp_arr(set, set);
  Term set_set_prop = mk_tp_arr(set, mk_tp_arr(set, prop));
  /* 0: Choice : Pi A. (A -> prop) -> A */
  Term v0 = mk_tp_var(0);
  prim_types[0] = mk_tp_all(mk_tp_arr(mk_tp_arr(v0, prop), v0));
  if (profile == PROF_HOAS) {
    nprims = 1;
  } else {
    /* 1: In : set -> set -> prop */
    prim_types[1] = set_set_prop;
    /* 3: Union : set -> set */
    prim_types[3] = set_set;
    if (profile == PROF_MIZAR) {
      nprims = 4;
    } else {
      /* 2: Empty : set */
      prim_types[2] = set;
      /* 4: Power : set -> set */
      prim_types[4] = set_set;
      /* 5: Repl : set -> (set -> set) -> set */
      prim_types[5] = mk_tp_arr(set, mk_tp_arr(set_set, set));
      if (profile == PROF_EGAL) {
        /* 6: UnivOf : set -> set */
        prim_types[6] = set_set;
        nprims = 7;
      } else {
        nprims = 6;
      }
    }
  }
  for (uint32_t j = 0; j < nprims; j++) {
    if (prim_types[j]) {
      Term a[2] = { mk_int(j), prim_types[j] };
      prim_sig_occs[j] = tc_post(SPACE_SIG, tc_app(C_SIG_PRIM, a));
    }
  }
}

/* ---- Type well-formedness, term typing, and propositionhood via tcalc rules in SPACE_THM ---- */
static Occ prove_plain_wf(uint32_t depth, Term tp) {
  if (!tp || !tp_plain_wf(tp, depth)) return 0;
  Occ hit = op_cache_get_occ(OP_WF, tp, 0, depth, NULL);
  if (hit) return hit;
  Term d_t = mk_int(depth);
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  int hc = (int)h;
  Occ occ = 0;
  if (hc == C_TP_PROP) {
    Term inst[1] = { d_t };
    occ = commit_mg_step(R_WF_PROP, NULL, inst);
  } else if (hc == C_TP_BASE) {
    Term inst[2] = { d_t, a[0] };
    occ = commit_mg_step(R_WF_BASE, NULL, inst);
  } else if (hc == C_TP_VAR) {
    uint32_t idx = int_val(a[0]);
    if (idx < depth) {
      Term ha[2] = { a[0], d_t };
      Occ hocc = tc_post(SPACE_HELPER, tc_app(C_HELPER_LT, ha));
      Occ keep[1] = { hocc };
      Term inst[2] = { d_t, a[0] };
      occ = commit_mg_step(R_WF_VAR, keep, inst);
    }
  } else if (hc == C_TP_ARR) {
    Term dom = a[0], cod = a[1];
    Occ o_dom = prove_plain_wf(depth, dom);
    Occ o_cod = o_dom ? prove_plain_wf(depth, cod) : 0;
    if (o_cod) {
      Occ keep[2] = { o_dom, o_cod };
      Term inst[3] = { d_t, dom, cod };
      occ = commit_mg_step(R_WF_ARR, keep, inst);
    }
  }
  if (occ) op_cache_put_occ(OP_WF, tp, 0, depth, tp, occ);
  return occ;
}

static Occ prove_has_type(uint32_t depth, Term tpl, Term m, Term *out_tp) {
  if (out_tp) *out_tp = 0;
  if (!m) return 0;
  Term cached_tp = 0;
  Occ hit = op_cache_get_occ(OP_INFER, m, tpl, depth, &cached_tp);
  if (hit) {
    if (out_tp) *out_tp = cached_tp;
    return hit;
  }
  Term d_t = mk_int(depth);
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  Term r = 0;
  Occ occ = 0;
  if (hc == C_TM_DB) {
    Term tp = list_nth(tpl, C_TPLC, int_val(a[0]));
    if (tp) {
      Term ha[3] = { tpl, a[0], tp };
      Occ hocc = tc_post(SPACE_HELPER, tc_app(C_HELPER_TPL_LOOKUP, ha));
      Occ keep[1] = { hocc };
      Term inst[4] = { d_t, tpl, a[0], tp };
      occ = commit_mg_step(R_TY_DB, keep, inst);
      if (occ) r = tp;
    }
  } else if (hc == C_TM_PRIM) {
    uint32_t idx = int_val(a[0]);
    if (idx < nprims && prim_sig_occs[idx]) {
      Occ keep[1] = { prim_sig_occs[idx] };
      Term inst[4] = { d_t, tpl, a[0], prim_types[idx] };
      occ = commit_mg_step(R_TY_PRIM, keep, inst);
      if (occ) r = prim_types[idx];
    }
  } else if (hc == C_TM_NAME) {
    uint32_t id = meta_of(a[0])->uval;
    if (id <= nsyms && syms[id].has_term && syms[id].sig_occ) {
      Occ keep[1] = { syms[id].sig_occ };
      Term inst[4] = { d_t, tpl, a[0], syms[id].tp };
      occ = commit_mg_step(R_TY_NAME, keep, inst);
      if (occ) r = syms[id].tp;
    }
  } else if (hc == C_TM_AP) {
    Term f = a[0], x = a[1], tf = 0, tx = 0;
    Occ of = prove_has_type(depth, tpl, f, &tf);
    if (of) {
      uint8_t tk; uint32_t th; int tar; const Term *ta;
      tc_node(tf, &tk, &th, &tar, &ta);
      if ((int)th == C_TP_ARR) {
        Term dom = ta[0], cod = ta[1];
        Occ ox = prove_has_type(depth, tpl, x, &tx);
        if (ox && tx == dom) {
          Occ keep[2] = { of, ox };
          Term inst[6] = { d_t, tpl, f, x, dom, cod };
          occ = commit_mg_step(R_TY_AP, keep, inst);
          if (occ) r = cod;
        }
      }
    }
  } else if (hc == C_TM_TAP) {
    Term f = a[0], tp = a[1], tf = 0;
    Occ owf = prove_plain_wf(depth, tp);
    Occ of = owf ? prove_has_type(depth, tpl, f, &tf) : 0;
    if (of) {
      uint8_t tk; uint32_t th; int tar; const Term *ta;
      tc_node(tf, &tk, &th, &tar, &ta);
      if ((int)th == C_TP_ALL) {
        Term body_tp = ta[0];
        Term res_tp = tp_instantiate(body_tp, 0, tp);
        Term ha[3] = { body_tp, tp, res_tp };
        Occ hocc = tc_post(SPACE_HELPER, tc_app(C_HELPER_TP_INST0, ha));
        Occ keep[3] = { of, owf, hocc };
        Term inst[6] = { d_t, tpl, f, body_tp, tp, res_tp };
        occ = commit_mg_step(R_TY_TAP, keep, inst);
        if (occ) r = res_tp;
      }
    }
  } else if (hc == C_TM_LAM) {
    Term tp = a[0], b = a[1], tb = 0;
    Occ owf = prove_plain_wf(depth, tp);
    Occ ob = owf ? prove_has_type(depth, mk_tplc(tp, tpl), b, &tb) : 0;
    if (ob) {
      Occ keep[2] = { owf, ob };
      Term inst[5] = { d_t, tpl, tp, b, tb };
      occ = commit_mg_step(R_TY_LAM, keep, inst);
      if (occ) r = mk_tp_arr(tp, tb);
    }
  } else if (hc == C_TM_TLAM) {
    Term b = a[0], tb = 0;
    uint32_t d1 = depth + 1u;
    Term d1_t = mk_int(d1);
    Term tpl1 = tpl_shift1(tpl);
    Occ ob = prove_has_type(d1, tpl1, b, &tb);
    if (ob) {
      Term ha[4] = { d_t, tpl, d1_t, tpl1 };
      Occ hocc = tc_post(SPACE_HELPER, tc_app(C_HELPER_TPL_SHIFT1, ha));
      Occ keep[2] = { hocc, ob };
      Term inst[6] = { d_t, tpl, d1_t, tpl1, b, tb };
      occ = commit_mg_step(R_TY_TLAM, keep, inst);
      if (occ) r = mk_tp_all(tb);
    }
  } else if (hc == C_TM_IMP) {
    Term p = a[0], q = a[1], tp_p = 0, tp_q = 0;
    Occ op = prove_has_type(depth, tpl, p, &tp_p);
    Occ oq = (op && tp_p == T_TP_PROP) ? prove_has_type(depth, tpl, q, &tp_q) : 0;
    if (oq && tp_q == T_TP_PROP) {
      Occ keep[2] = { op, oq };
      Term inst[4] = { d_t, tpl, p, q };
      occ = commit_mg_step(R_TY_IMP, keep, inst);
      if (occ) r = T_TP_PROP;
    }
  } else if (hc == C_TM_ALL) {
    Term tp = a[0], b = a[1], tp_b = 0;
    Occ owf = prove_plain_wf(depth, tp);
    Occ ob = owf ? prove_has_type(depth, mk_tplc(tp, tpl), b, &tp_b) : 0;
    if (ob && tp_b == T_TP_PROP) {
      Occ keep[2] = { owf, ob };
      Term inst[4] = { d_t, tpl, tp, b };
      occ = commit_mg_step(R_TY_ALL, keep, inst);
      if (occ) r = T_TP_PROP;
    }
  }
  if (occ && r) {
    op_cache_put_occ(OP_INFER, m, tpl, depth, r, occ);
    if (out_tp) *out_tp = r;
  }
  return occ;
}

static Occ prove_is_prop(uint32_t depth, Term tpl, Term m) {
  if (!m) return 0;
  Occ hit = op_cache_get_occ(OP_PROP, m, tpl, depth, NULL);
  if (hit) return hit;
  Term d_t = mk_int(depth);
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  Occ occ = 0;
  if ((int)h == C_TM_TALL) {
    uint32_t d1 = depth + 1u;
    Term d1_t = mk_int(d1);
    Occ ob = prove_is_prop(d1, T_TPLN, a[0]);
    if (ob) {
      Term ha[4] = { d_t, tpl, d1_t, T_TPLN };
      Occ hocc = tc_post(SPACE_HELPER, tc_app(C_HELPER_TPL_SHIFT1, ha));
      Occ keep[2] = { hocc, ob };
      Term inst[4] = { d_t, tpl, d1_t, a[0] };
      occ = commit_mg_step(R_PROP_TALL, keep, inst);
    }
  } else {
    Term tp = 0;
    Occ oty = prove_has_type(depth, tpl, m, &tp);
    if (oty && tp == T_TP_PROP) {
      Occ keep[1] = { oty };
      Term inst[3] = { d_t, tpl, m };
      occ = commit_mg_step(R_PROP_BASE, keep, inst);
    }
  }
  if (occ) op_cache_put_occ(OP_PROP, m, tpl, depth, m, occ);
  return occ;
}

/* ---- Lazy WHNF & Conversion (beta-delta-eta) ---- */
typedef struct {
  Term arg;
  bool is_type;
} SpineArg;

typedef struct {
  SpineArg *args;
  uint32_t len, cap;
  Term head;
} Spine;

static void spine_of(Spine *sp, Term m) {
  uint32_t n = 0;
  for (Term t = m;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(t, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP && (int)h != C_TM_TAP) break;
    t = a[0];
    n++;
  }
  if (n > sp->cap) {
    sp->args = realloc(sp->args, (size_t)n * sizeof(SpineArg));
    sp->cap = n;
  }
  sp->len = n;
  Term t = m;
  for (uint32_t i = n; i > 0; i--) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(t, &k, &h, &ar, &a);
    sp->args[i - 1] = (SpineArg){ a[1], (int)h == C_TM_TAP };
    t = a[0];
  }
  sp->head = t;
}

static Term spine_build(Term head, const SpineArg *args, uint32_t from, uint32_t to) {
  Term m = head;
  for (uint32_t i = from; i < to; i++) {
    m = args[i].is_type ? mk_tm_tap(m, args[i].arg) : mk_tm_ap(m, args[i].arg);
  }
  return m;
}

static uint32_t defined_head_sym(Term head) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(head, &k, &h, &ar, &a);
  if ((int)h != C_TM_NAME) return 0;
  uint32_t id = meta_of(a[0])->uval;
  return (id <= nsyms && syms[id].has_term && syms[id].def) ? id : 0;
}

static uint32_t head_def_sym(Term m) {
  for (;;) {
    uint8_t k; uint32_t h; int ar; const Term *a;
    tc_node(m, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP && (int)h != C_TM_TAP) return defined_head_sym(m);
    m = a[0];
  }
}

static Term whnf_beta(Term m) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  if ((int)h != C_TM_AP && (int)h != C_TM_TAP) return m;
  Spine sp = {0};
  for (;;) {
    tc_node(m, &k, &h, &ar, &a);
    if ((int)h != C_TM_AP && (int)h != C_TM_TAP) break;
    spine_of(&sp, m);
    tc_node(sp.head, &k, &h, &ar, &a);
    Term red = 0;
    if ((int)h == C_TM_LAM && !sp.args[0].is_type)
      red = tm_instantiate(a[1], 0, sp.args[0].arg);
    else if ((int)h == C_TM_TLAM && sp.args[0].is_type)
      red = tm_tinstantiate(a[0], 0, sp.args[0].arg);
    else
      break;
    m = spine_build(red, sp.args, 1, sp.len);
  }
  free(sp.args);
  return m;
}

static Term unfold_head(Term m) {
  Spine sp = {0};
  spine_of(&sp, m);
  uint32_t id = defined_head_sym(sp.head);
  if (id) syms[id].unfolded = true;
  Term r = id ? spine_build(syms[id].def, sp.args, 0, sp.len) : 0;
  free(sp.args);
  return r;
}

static Term mg_whnf(Term m) {
  for (;;) {
    m = whnf_beta(m);
    if (!head_def_sym(m)) return m;
    m = unfold_head(m);
  }
}

static bool is_structure_con(int hc) {
  return hc == C_TM_LAM || hc == C_TM_ALL || hc == C_TM_IMP ||
         hc == C_TM_TLAM || hc == C_TM_TALL;
}

typedef struct {
  Term a, b;
  uint8_t res; /* 1 = equal, 2 = not equal */
} ConvSlot;

typedef struct {
  ConvSlot *slots;
  size_t cap, len;
} ConvMemo;

static size_t conv_slot_idx(Term a, Term b, size_t cap) {
  uint64_t h = (uint64_t)a * 0x9e3779b97f4a7c15ULL ^
               (uint64_t)b * 0xc2b2ae3d27d4eb4fULL;
  h ^= h >> 29;
  return (size_t)h & (cap - 1u);
}

static uint8_t conv_memo_get(const ConvMemo *cm, Term a, Term b) {
  if (!cm->cap) return 0;
  for (size_t i = conv_slot_idx(a, b, cm->cap);; i = (i + 1) & (cm->cap - 1)) {
    if (!cm->slots[i].a) return 0;
    if (cm->slots[i].a == a && cm->slots[i].b == b) return cm->slots[i].res;
  }
}

static void conv_memo_put(ConvMemo *cm, Term a, Term b, bool eq) {
  if ((cm->len + 1) * 2 > cm->cap) {
    size_t nc = cm->cap ? cm->cap * 2 : 256;
    ConvSlot *ns = calloc(nc, sizeof(ConvSlot));
    for (size_t j = 0; j < cm->cap; j++) {
      if (!cm->slots[j].a) continue;
      size_t k = conv_slot_idx(cm->slots[j].a, cm->slots[j].b, nc);
      while (ns[k].a) k = (k + 1) & (nc - 1);
      ns[k] = cm->slots[j];
    }
    free(cm->slots);
    cm->slots = ns;
    cm->cap = nc;
  }
  size_t i = conv_slot_idx(a, b, cm->cap);
  while (cm->slots[i].a) i = (i + 1) & (cm->cap - 1);
  cm->slots[i] = (ConvSlot){ a, b, (uint8_t)(eq ? 1 : 2) };
  cm->len++;
}

static bool conv_rec(ConvMemo *cm, Term a, Term b) {
  if (a == b) return true;
  uint8_t hit = conv_memo_get(cm, a, b);
  if (hit) return hit == 1;
  Term key_a = a, key_b = b;
  bool result = false;
  for (;;) {
    a = whnf_beta(a);
    b = whnf_beta(b);
    if (a == b) { result = true; break; }
    uint8_t ak, bk; uint32_t ah, bh; int aar, bar; const Term *aa, *ba;
    tc_node(a, &ak, &ah, &aar, &aa);
    Term a0 = aar > 0 ? aa[0] : 0, a1 = aar > 1 ? aa[1] : 0;
    tc_node(b, &bk, &bh, &bar, &ba);
    Term b0 = bar > 0 ? ba[0] : 0, b1 = bar > 1 ? ba[1] : 0;
    int ha = (int)ah, hb = (int)bh;
    if (ha == C_TM_LAM && hb == C_TM_LAM) {
      result = (a0 == b0) && conv_rec(cm, a1, b1);
      break;
    }
    if (ha == C_TM_TLAM && hb == C_TM_TLAM) {
      result = conv_rec(cm, a0, b0);
      break;
    }
    if (ha == C_TM_LAM || hb == C_TM_LAM || ha == C_TM_TLAM || hb == C_TM_TLAM) {
      bool left = (ha == C_TM_LAM || ha == C_TM_TLAM);
      int hlam = left ? ha : hb;
      int hother = left ? hb : ha;
      Term lam_body = left ? (ha == C_TM_LAM ? a1 : a0) : (hb == C_TM_LAM ? b1 : b0);
      Term other = left ? b : a;
      if (is_structure_con(hother)) break;
      Term app = (hlam == C_TM_LAM)
                   ? mk_tm_ap(tm_shift(other, 0, 1), mk_tm_db(0))
                   : mk_tm_tap(tm_tshift(other, 0, 1), mk_tp_var(0));
      result = conv_rec(cm, lam_body, app);
      break;
    }
    bool sa = is_structure_con(ha), sb = is_structure_con(hb);
    if (sa && sb) {
      if (ha != hb) break;
      if (ha == C_TM_ALL) result = (a0 == b0) && conv_rec(cm, a1, b1);
      else if (ha == C_TM_IMP) result = conv_rec(cm, a0, b0) && conv_rec(cm, a1, b1);
      else if (ha == C_TM_TALL) result = conv_rec(cm, a0, b0);
      break;
    }
    if (sa || sb) {
      Term neutral = sa ? b : a;
      if (!head_def_sym(neutral)) break;
      Term u = unfold_head(neutral);
      if (sa) b = u; else a = u;
      continue;
    }
    Spine sx = {0}, sy = {0};
    spine_of(&sx, a);
    spine_of(&sy, b);
    bool same_args = (sx.head == sy.head && sx.len == sy.len);
    for (uint32_t i = 0; same_args && i < sx.len; i++) {
      if (sx.args[i].is_type != sy.args[i].is_type) same_args = false;
      else if (sx.args[i].is_type) same_args = (sx.args[i].arg == sy.args[i].arg);
      else same_args = conv_rec(cm, sx.args[i].arg, sy.args[i].arg);
    }
    uint32_t da = defined_head_sym(sx.head);
    uint32_t db = defined_head_sym(sy.head);
    free(sx.args);
    free(sy.args);
    if (same_args) { result = true; break; }
    if (!da && !db) break;
    if (da && db) {
      if (da == db) { a = unfold_head(a); b = unfold_head(b); }
      else if (syms[da].term_seq >= syms[db].term_seq) a = unfold_head(a);
      else b = unfold_head(b);
    } else if (da) {
      a = unfold_head(a);
    } else {
      b = unfold_head(b);
    }
  }
  conv_memo_put(cm, key_a, key_b, result);
  return result;
}

static bool mg_conv(Term a, Term b) {
  if (a == b) return true;
  ConvMemo cm = {0};
  bool r = conv_rec(&cm, a, b);
  free(cm.slots);
  return r;
}

/* ---- Proof AST ---- */
enum {
  PF_GPA = 1, PF_HYP, PF_KNOWN, PF_TMAP, PF_PFAP,
  PF_PLAM, PF_TLAM, PF_TPAP, PF_TPLAM
};
typedef struct MgPf {
  uint8_t tag;
  uint32_t n;       /* HYP index or KNOWN/GPA sym id */
  struct MgPf *p, *q;
  Term t;           /* TMAP arg or PLAM source prop */
  Term tp;          /* TLAM type or TPAP type */
} MgPf;

typedef struct PfChunk {
  struct PfChunk *next;
  size_t used;
  MgPf nodes[4096];
} PfChunk;

static PfChunk *pf_chunks;

static MgPf *alloc_pf(uint8_t tag) {
  if (!pf_chunks || pf_chunks->used == 4096) {
    PfChunk *c = calloc(1, sizeof(PfChunk));
    c->next = pf_chunks;
    pf_chunks = c;
  }
  MgPf *p = &pf_chunks->nodes[pf_chunks->used++];
  p->tag = tag;
  return p;
}

static void free_pf_chunks(void) {
  while (pf_chunks) {
    PfChunk *n = pf_chunks->next;
    free(pf_chunks);
    pf_chunks = n;
  }
}

/* ---- Firing the 8 Megalodon rules on tcalc ---- */
typedef struct {
  const MgPf *pf;
  Term ctx;
  Term prop;
  Occ  occ;
} PfMemoSlot;

typedef struct {
  PfMemoSlot *slots;
  size_t cap, len;
} PfMemo;

static size_t pf_memo_idx(const MgPf *pf, Term ctx, size_t cap) {
  uint64_t h = (uint64_t)(uintptr_t)pf * 0x9e3779b97f4a7c15ULL ^
               (uint64_t)ctx * 0xc2b2ae3d27d4eb4fULL;
  h ^= h >> 29;
  return (size_t)h & (cap - 1u);
}

static const PfMemoSlot *pf_memo_get(const PfMemo *pm, const MgPf *pf, Term ctx) {
  if (!pm->cap) return NULL;
  for (size_t i = pf_memo_idx(pf, ctx, pm->cap);; i = (i + 1) & (pm->cap - 1)) {
    if (!pm->slots[i].pf) return NULL;
    if (pm->slots[i].pf == pf && pm->slots[i].ctx == ctx) return &pm->slots[i];
  }
}

static void pf_memo_put(PfMemo *pm, const MgPf *pf, Term ctx, Term prop, Occ occ) {
  if ((pm->len + 1) * 2 > pm->cap) {
    size_t nc = pm->cap ? pm->cap * 2 : 256;
    PfMemoSlot *ns = calloc(nc, sizeof(PfMemoSlot));
    for (size_t j = 0; j < pm->cap; j++) {
      if (!pm->slots[j].pf) continue;
      size_t k = pf_memo_idx(pm->slots[j].pf, pm->slots[j].ctx, nc);
      while (ns[k].pf) k = (k + 1) & (nc - 1);
      ns[k] = pm->slots[j];
    }
    free(pm->slots);
    pm->slots = ns;
    pm->cap = nc;
  }
  size_t i = pf_memo_idx(pf, ctx, pm->cap);
  while (pm->slots[i].pf) i = (i + 1) & (pm->cap - 1);
  pm->slots[i] = (PfMemoSlot){ pf, ctx, prop, occ };
  pm->len++;
}

static uint64_t stat_rule_fires[9];

static Occ check_pf_rec(PfMemo *pm, Term ctx, const MgPf *pf, Term *out_prop) {
  *out_prop = 0;
  if (!pf) return 0;
  const PfMemoSlot *hit = pf_memo_get(pm, pf, ctx);
  if (hit) {
    *out_prop = hit->prop;
    return hit->occ;
  }
  uint32_t depth; Term tpl, tml;
  unpack_ctx(ctx, &depth, &tpl, &tml);
  Term d_t = mk_int(depth);
  Occ res_occ = 0;
  Term res_prop = 0;

  switch (pf->tag) {
  case PF_GPA:
    /* Automation placeholder is never a valid proof */
    return 0;

  case PF_HYP: {
    Term h = list_nth(tml, C_TMLC, pf->n);
    if (!h) return 0;
    Term idx_t = mk_int(pf->n);
    Term ha[3] = { tml, idx_t, h };
    Occ hocc = tc_post(SPACE_HELPER, tc_app(C_HELPER_TML_LOOKUP, ha));
    Occ keep[1] = { hocc };
    Term inst[5] = { d_t, tpl, tml, idx_t, h };
    res_occ = commit_mg_step(R_HYP, keep, inst);
    if (res_occ) { res_prop = h; stat_rule_fires[1]++; }
    break;
  }

  case PF_KNOWN: {
    if (pf->n == 0 || pf->n > nsyms || !syms[pf->n].has_known) return 0;
    Term p = syms[pf->n].prop;
    Term nt = syms[pf->n].nterm;
    Occ keep[2] = { syms[pf->n].known_sig_occ, syms[pf->n].known_occ };
    Term inst[3] = { ctx, nt, p };
    res_occ = commit_mg_step(R_KNOWN, keep, inst);
    if (res_occ) { res_prop = p; stat_rule_fires[2]++; }
    break;
  }

  case PF_TMAP: {
    Term qprop = 0;
    Occ qocc = check_pf_rec(pm, ctx, pf->p, &qprop);
    if (!qocc) return 0;
    Term h = mg_whnf(qprop);
    uint8_t hk; uint32_t hh; int har; const Term *ha;
    tc_node(h, &hk, &hh, &har, &ha);
    if ((int)hh != C_TM_ALL) return 0;
    Term dom_tp = ha[0], body = ha[1];
    Term actual_tp = 0;
    Occ o_arg = prove_has_type(depth, tpl, pf->t, &actual_tp);
    if (!o_arg || actual_tp != dom_tp) return 0;
    Term concl = tm_instantiate(body, 0, pf->t);
    Term ca[2] = { qprop, h };
    Occ c_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_CONV, ca));
    Term ia[3] = { body, pf->t, concl };
    Occ i_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_TM_INST0, ia));
    Occ keep[4] = { qocc, c_occ, o_arg, i_occ };
    Term inst[8] = { d_t, tpl, tml, qprop, dom_tp, body, pf->t, concl };
    res_occ = commit_mg_step(R_TERM_APP, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[3]++; }
    break;
  }

  case PF_PFAP: {
    Term iprop = 0;
    Occ iocc = check_pf_rec(pm, ctx, pf->p, &iprop);
    if (!iocc) return 0;
    Term h = mg_whnf(iprop);
    uint8_t hk; uint32_t hh; int har; const Term *ha;
    tc_node(h, &hk, &hh, &har, &ha);
    if ((int)hh != C_TM_IMP) return 0;
    Term dom = ha[0], concl = ha[1];
    Term aprop = 0;
    Occ aocc = check_pf_rec(pm, ctx, pf->q, &aprop);
    if (!aocc) return 0;
    if (!mg_conv(aprop, dom)) return 0;
    Term ca[2] = { iprop, mk_tm_imp(aprop, concl) };
    Occ c_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_CONV, ca));
    Occ keep[3] = { iocc, aocc, c_occ };
    Term inst[4] = { ctx, iprop, aprop, concl };
    res_occ = commit_mg_step(R_PROOF_APP, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[4]++; }
    break;
  }

  case PF_TLAM: {
    Occ owf = prove_plain_wf(depth, pf->tp);
    if (!owf) return 0;
    Term tml1 = tml_shift1(tml);
    Term inner = mk_ctx(depth, mk_tplc(pf->tp, tpl), tml1);
    Term bprop = 0;
    Occ bocc = check_pf_rec(pm, inner, pf->p, &bprop);
    if (!bocc) return 0;
    Term concl = mk_tm_all(pf->tp, bprop);
    Term sa[2] = { tml, tml1 };
    Occ s_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_TML_SHIFT1, sa));
    Occ keep[3] = { owf, s_occ, bocc };
    Term inst[6] = { d_t, tpl, tml, pf->tp, tml1, bprop };
    res_occ = commit_mg_step(R_TERM_LAM, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[5]++; }
    break;
  }

  case PF_PLAM: {
    Term src_tp = 0;
    Occ o_src = prove_has_type(depth, tpl, pf->t, &src_tp);
    if (!o_src || src_tp != T_TP_PROP) return 0;
    Term inner = mk_ctx(depth, tpl, mk_tmlc(pf->t, tml));
    Term bprop = 0;
    Occ bocc = check_pf_rec(pm, inner, pf->p, &bprop);
    if (!bocc) return 0;
    Term concl = mk_tm_imp(pf->t, bprop);
    Occ keep[2] = { o_src, bocc };
    Term inst[5] = { d_t, tpl, tml, pf->t, bprop };
    res_occ = commit_mg_step(R_PROOF_LAM, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[6]++; }
    break;
  }

  case PF_TPAP: {
    Occ owf = prove_plain_wf(depth, pf->tp);
    if (!owf) return 0;
    Term qprop = 0;
    Occ qocc = check_pf_rec(pm, ctx, pf->p, &qprop);
    if (!qocc) return 0;
    Term h = mg_whnf(qprop);
    uint8_t hk; uint32_t hh; int har; const Term *ha;
    tc_node(h, &hk, &hh, &har, &ha);
    if ((int)hh != C_TM_TALL) return 0;
    Term body = ha[0];
    Term concl = tm_tinstantiate(body, 0, pf->tp);
    Term ca[2] = { qprop, h };
    Occ c_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_CONV, ca));
    Term ia[3] = { body, pf->tp, concl };
    Occ i_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_TINST0, ia));
    Occ keep[4] = { qocc, c_occ, owf, i_occ };
    Term inst[7] = { d_t, tpl, tml, qprop, body, pf->tp, concl };
    res_occ = commit_mg_step(R_TYPE_APP, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[7]++; }
    break;
  }

  case PF_TPLAM: {
    if (tpl != T_TPLN || tml != T_TMLN) return 0;
    uint32_t d1 = depth + 1u;
    Term d1_t = mk_int(d1);
    Term inner = mk_ctx(d1, T_TPLN, T_TMLN);
    Term bprop = 0;
    Occ bocc = check_pf_rec(pm, inner, pf->p, &bprop);
    if (!bocc) return 0;
    Term concl = mk_tm_tall(bprop);
    Term sa[4] = { d_t, T_TPLN, d1_t, T_TPLN };
    Occ s_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_TPL_SHIFT1, sa));
    Occ keep[2] = { s_occ, bocc };
    Term inst[3] = { d_t, d1_t, bprop };
    res_occ = commit_mg_step(R_TYPE_LAM, keep, inst);
    if (res_occ) { res_prop = concl; stat_rule_fires[8]++; }
    break;
  }
  }

  if (res_occ && res_prop) {
    pf_memo_put(pm, pf, ctx, res_prop, res_occ);
    *out_prop = res_prop;
  }
  return res_occ;
}

static Occ check_proof_tree(Term ctx, const MgPf *pf, Term *out_prop) {
  PfMemo pm = {0};
  Occ o = check_pf_rec(&pm, ctx, pf, out_prop);
  free(pm.slots);
  return o;
}

/* ---- Initialize tcalc sorts, constructors, and sealed rules ---- */
static void init_mg_kernel(int profile) {
  tc_init(1u << 23, 1u << 22);
  memset(op_cache, 0, sizeof(op_cache));
  memset(stat_rule_fires, 0, sizeof(stat_rule_fires));
  free(NMETA); NMETA = NULL; nmeta_cap = 0;
  free(int_terms); int_terms = NULL; int_terms_cap = 0;
  for (uint32_t i = 1; i <= nsyms; i++) free(syms[i].text);
  free(syms); syms = NULL; nsyms = capsyms = 0;
  free(sym_tab); sym_tab = NULL; sym_tab_cap = 0;
  next_decl_seq = 1;
  T_TP_PROP = T_TP_SET = T_TPLN = T_TMLN = T_CTX_EMPTY = 0;

  S_INT    = tc_sort(SORT_PURE | SORT_FREE);
  S_NAME   = tc_sort(SORT_PURE | SORT_FREE);
  S_TP     = tc_sort(0);
  S_TM     = tc_sort(0);
  S_TPL    = tc_sort(0);
  S_TML    = tc_sort(0);
  S_CTX    = tc_sort(0);
  S_SIG    = tc_sort(SORT_PROVABLE);
  S_HELPER = tc_sort(SORT_PROVABLE);
  S_THM    = tc_sort(SORT_PROVABLE);
  S_HANDLE = tc_sort(0);
  uint16_t sp_sort = tc_space_sort();

  Binder b_int[1]  = { { (uint16_t)S_INT, 0, 0 } };
  Binder b_int2[2] = { { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_INT, 0, 0 } };
  Binder b_nam[1]  = { { (uint16_t)S_NAME, 0, 0 } };
  Binder b_tp1[1]  = { { (uint16_t)S_TP, 0, 0 } };
  Binder b_tp2[2]  = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_tp3[3]  = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_tm1[1]  = { { (uint16_t)S_TM, 0, 0 } };
  Binder b_tm2[2]  = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  Binder b_tm3[3]  = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  Binder b_tptm[2] = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  Binder b_tmtp[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_tmtptm[3] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };

  C_TP_PROP = tc_con((uint16_t)S_TP, 0, 0, NULL);
  C_TP_BASE = tc_con((uint16_t)S_TP, 0, 1, b_int);
  C_TP_VAR  = tc_con((uint16_t)S_TP, 0, 1, b_int);
  C_TP_ARR  = tc_con((uint16_t)S_TP, 0, 2, b_tp2);
  C_TP_ALL  = tc_con((uint16_t)S_TP, 0, 1, b_tp1);

  C_TM_DB   = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_NAME = tc_con((uint16_t)S_TM, 0, 1, b_nam);
  C_TM_PRIM = tc_con((uint16_t)S_TM, 0, 1, b_int);
  C_TM_AP   = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
  C_TM_LAM  = tc_con((uint16_t)S_TM, 0, 2, b_tptm);
  C_TM_IMP  = tc_con((uint16_t)S_TM, 0, 2, b_tm2);
  C_TM_ALL  = tc_con((uint16_t)S_TM, 0, 2, b_tptm);
  C_TM_TAP  = tc_con((uint16_t)S_TM, 0, 2, b_tmtp);
  C_TM_TLAM = tc_con((uint16_t)S_TM, 0, 1, b_tm1);
  C_TM_TALL = tc_con((uint16_t)S_TM, 0, 1, b_tm1);

  Binder b_tplc[2] = { { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TPL, 0, 0 } };
  Binder b_tmlc[2] = { { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TML, 0, 0 } };
  Binder b_ctx[3]  = {
    { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 }, { (uint16_t)S_TML, 0, 0 }
  };
  C_TPLN = tc_con((uint16_t)S_TPL, 0, 0, NULL);
  C_TPLC = tc_con((uint16_t)S_TPL, 0, 2, b_tplc);
  C_TMLN = tc_con((uint16_t)S_TML, 0, 0, NULL);
  C_TMLC = tc_con((uint16_t)S_TML, 0, 2, b_tmlc);
  C_CTX  = tc_con((uint16_t)S_CTX, 0, 3, b_ctx);

  /* Protected SPACE_THM judgment constructors */
  Binder b_wf[2]   = { { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_ty[4]   = {
    { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
    { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TP, 0, 0 }
  };
  Binder b_prop[3] = {
    { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_thm[2]  = { { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  C_PLAIN_WF = tc_con((uint16_t)S_THM, 0, 2, b_wf);
  C_HAS_TYPE = tc_con((uint16_t)S_THM, 0, 4, b_ty);
  C_IS_PROP  = tc_con((uint16_t)S_THM, 0, 3, b_prop);
  C_THM      = tc_con((uint16_t)S_THM, 0, 2, b_thm);

  /* Protected SPACE_SIG declaration constructors */
  Binder b_sprim[2] = { { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_sterm[2] = { { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TP, 0, 0 } };
  Binder b_kthm[2]  = { { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
  C_SIG_PRIM  = tc_con((uint16_t)S_SIG, 0, 2, b_sprim);
  C_SIG_TERM  = tc_con((uint16_t)S_SIG, 0, 2, b_sterm);
  C_KNOWN_THM = tc_con((uint16_t)S_SIG, 0, 2, b_kthm);

  /* Named, ledgered C helper constructors in SPACE_HELPER */
  Binder b_tpl_lk[3] = {
    { (uint16_t)S_TPL, 0, 0 }, { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
  };
  Binder b_tml_lk[3] = {
    { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
  };
  Binder b_tpl_sh[4] = {
    { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
    { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 }
  };
  Binder b_tml_sh[2] = { { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_TML, 0, 0 } };
  C_HELPER_CONV       = tc_con((uint16_t)S_HELPER, 0, 2, b_tm2);
  C_HELPER_LT         = tc_con((uint16_t)S_HELPER, 0, 2, b_int2);
  C_HELPER_TPL_LOOKUP = tc_con((uint16_t)S_HELPER, 0, 3, b_tpl_lk);
  C_HELPER_TML_LOOKUP = tc_con((uint16_t)S_HELPER, 0, 3, b_tml_lk);
  C_HELPER_TPL_SHIFT1 = tc_con((uint16_t)S_HELPER, 0, 4, b_tpl_sh);
  C_HELPER_TML_SHIFT1 = tc_con((uint16_t)S_HELPER, 0, 2, b_tml_sh);
  C_HELPER_TP_INST0   = tc_con((uint16_t)S_HELPER, 0, 3, b_tp3);
  C_HELPER_TM_INST0   = tc_con((uint16_t)S_HELPER, 0, 3, b_tm3);
  C_HELPER_TINST0     = tc_con((uint16_t)S_HELPER, 0, 3, b_tmtptm);

  /* NamedSpaces / SpacesCreation / NamedSpacesReach subproof & actuator constructors */
  Binder b_sp[1] = { { sp_sort, 0, 0 } };
  C_HANDLE     = tc_con((uint16_t)S_HANDLE, 0, 1, b_sp);
  C_SUB_MARK   = tc_con((uint16_t)S_HELPER, 0, 1, b_sp);
  C_SUB_HYP    = tc_con((uint16_t)S_HELPER, 0, 2, b_thm);
  C_SUB_AUTH   = tc_con((uint16_t)S_HELPER, 0, 2, b_thm);
  C_ACT_REQ    = tc_con((uint16_t)S_HELPER, 0, 1, b_tm1);
  C_ACT_COMMIT = tc_con((uint16_t)S_HELPER, 0, 1, b_tm1);
  tc_set_handle_con(C_HANDLE);

  T_TP_PROP   = tc_app(C_TP_PROP, NULL);
  meta_of(T_TP_PROP)->init = 1;
  meta_of(T_TP_PROP)->plain = 1;
  T_TPLN      = tc_app(C_TPLN, NULL);
  T_TMLN      = tc_app(C_TMLN, NULL);
  Term a_empty[3] = { mk_int(0), T_TPLN, T_TMLN };
  T_CTX_EMPTY = tc_app(C_CTX, a_empty);

  init_profile_prims(profile);

  /* ---- 1. Type well-formedness rules in SPACE_THM ---- */
  {
    Binder v[1] = { { (uint16_t)S_INT, 0, 0 } };
    tc_ctx(1, v);
    Term wa[2] = { tc_v(0), T_TP_PROP };
    Rule r = { .nkeep = 0, .fresh = -1, .inputs = 0x1,   /* depth */ .make = { tc_app(C_PLAIN_WF, wa), SPACE_THM } };
    R_WF_PROP = tc_rule(&r);
  }
  {
    Binder v[2] = { { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_INT, 0, 0 } };
    tc_ctx(2, v);
    Term ba[1] = { tc_v(1) };
    Term wa[2] = { tc_v(0), tc_app(C_TP_BASE, ba) };
    Rule r = { .nkeep = 0, .fresh = -1, .inputs = 0x3,   /* depth, base index */ .make = { tc_app(C_PLAIN_WF, wa), SPACE_THM } };
    R_WF_BASE = tc_rule(&r);
  }
  {
    Binder v[2] = { { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_INT, 0, 0 } };
    tc_ctx(2, v);
    Term ha[2] = { tc_v(1), tc_v(0) };
    Term va[1] = { tc_v(1) };
    Term wa[2] = { tc_v(0), tc_app(C_TP_VAR, va) };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_HELPER_LT, ha), SPACE_HELPER } },
               .make = { tc_app(C_PLAIN_WF, wa), SPACE_THM } };
    R_WF_VAR = tc_rule(&r);
  }
  {
    Binder v[3] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(3, v);
    Term w0[2] = { tc_v(0), tc_v(1) };
    Term w1[2] = { tc_v(0), tc_v(2) };
    Term aa[2] = { tc_v(1), tc_v(2) };
    Term w2[2] = { tc_v(0), tc_app(C_TP_ARR, aa) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_PLAIN_WF, w0), SPACE_THM },
                         { tc_app(C_PLAIN_WF, w1), SPACE_THM } },
               .make = { tc_app(C_PLAIN_WF, w2), SPACE_THM } };
    R_WF_ARR = tc_rule(&r);
  }

  /* ---- 2. Term typing & propositionhood rules in SPACE_THM ---- */
  {
    /* R_TY_DB: keep HELPER_TPL_LOOKUP(tpl, idx, tp) |- HAS_TYPE(d, tpl, DB(idx), tp) */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(4, v);
    Term ha[3] = { tc_v(1), tc_v(2), tc_v(3) };
    Term da[1] = { tc_v(2) };
    Term ta[4] = { tc_v(0), tc_v(1), tc_app(C_TM_DB, da), tc_v(3) };
    Rule r = { .nkeep = 1, .fresh = -1, .inputs = 0x1,   /* depth */
               .keep = { { tc_app(C_HELPER_TPL_LOOKUP, ha), SPACE_HELPER } },
               .make = { tc_app(C_HAS_TYPE, ta), SPACE_THM } };
    R_TY_DB = tc_rule(&r);
  }
  {
    /* R_TY_PRIM: keep SIG_PRIM(idx, tp)@SPACE_SIG |- HAS_TYPE(d, tpl, Prim(idx), tp) */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(4, v);
    Term sa[2] = { tc_v(2), tc_v(3) };
    Term pa[1] = { tc_v(2) };
    Term ta[4] = { tc_v(0), tc_v(1), tc_app(C_TM_PRIM, pa), tc_v(3) };
    Rule r = { .nkeep = 1, .fresh = -1, .inputs = 0x3,   /* depth, type list */
               .keep = { { tc_app(C_SIG_PRIM, sa), SPACE_SIG } },
               .make = { tc_app(C_HAS_TYPE, ta), SPACE_THM } };
    R_TY_PRIM = tc_rule(&r);
  }
  {
    /* R_TY_NAME: keep SIG_TERM(name, tp)@SPACE_SIG |- HAS_TYPE(d, tpl, Name(name), tp) */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 },  { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(4, v);
    Term sa[2] = { tc_v(2), tc_v(3) };
    Term na[1] = { tc_v(2) };
    Term ta[4] = { tc_v(0), tc_v(1), tc_app(C_TM_NAME, na), tc_v(3) };
    Rule r = { .nkeep = 1, .fresh = -1, .inputs = 0x3,   /* depth, type list */
               .keep = { { tc_app(C_SIG_TERM, sa), SPACE_SIG } },
               .make = { tc_app(C_HAS_TYPE, ta), SPACE_THM } };
    R_TY_NAME = tc_rule(&r);
  }
  {
    /* R_TY_AP: keep HAS_TYPE(d, tpl, f, Arr(dom, cod)), HAS_TYPE(d, tpl, x, dom) |- HAS_TYPE(d, tpl, Ap(f, x), cod) */
    Binder v[6] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(6, v);
    Term ar_a[2] = { tc_v(4), tc_v(5) };
    Term t0[4]   = { tc_v(0), tc_v(1), tc_v(2), tc_app(C_TP_ARR, ar_a) };
    Term t1[4]   = { tc_v(0), tc_v(1), tc_v(3), tc_v(4) };
    Term ap_a[2] = { tc_v(2), tc_v(3) };
    Term t2[4]   = { tc_v(0), tc_v(1), tc_app(C_TM_AP, ap_a), tc_v(5) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_HAS_TYPE, t0), SPACE_THM },
                         { tc_app(C_HAS_TYPE, t1), SPACE_THM } },
               .make = { tc_app(C_HAS_TYPE, t2), SPACE_THM } };
    R_TY_AP = tc_rule(&r);
  }
  {
    /* R_TY_TAP: keep HAS_TYPE(d, tpl, f, TpAll(body_tp)), PLAIN_WF(d, arg_tp), HELPER_TP_INST0(body_tp, arg_tp, res_tp)
                 |- HAS_TYPE(d, tpl, TAp(f, arg_tp), res_tp) */
    Binder v[6] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TP, 0, 0 },
      { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(6, v);
    Term al_a[1] = { tc_v(3) };
    Term t0[4]   = { tc_v(0), tc_v(1), tc_v(2), tc_app(C_TP_ALL, al_a) };
    Term w0[2]   = { tc_v(0), tc_v(4) };
    Term h0[3]   = { tc_v(3), tc_v(4), tc_v(5) };
    Term tap[2]  = { tc_v(2), tc_v(4) };
    Term t1[4]   = { tc_v(0), tc_v(1), tc_app(C_TM_TAP, tap), tc_v(5) };
    Rule r = { .nkeep = 3, .fresh = -1,
               .keep = { { tc_app(C_HAS_TYPE, t0), SPACE_THM },
                         { tc_app(C_PLAIN_WF, w0), SPACE_THM },
                         { tc_app(C_HELPER_TP_INST0, h0), SPACE_HELPER } },
               .make = { tc_app(C_HAS_TYPE, t1), SPACE_THM } };
    R_TY_TAP = tc_rule(&r);
  }
  {
    /* R_TY_LAM: keep PLAIN_WF(d, dom), HAS_TYPE(d, TpLCons(dom, tpl), body, cod)
                 |- HAS_TYPE(d, tpl, Lam(dom, body), Arr(dom, cod)) */
    Binder v[5] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(5, v);
    Term w0[2]   = { tc_v(0), tc_v(2) };
    Term tplc[2] = { tc_v(2), tc_v(1) };
    Term t0[4]   = { tc_v(0), tc_app(C_TPLC, tplc), tc_v(3), tc_v(4) };
    Term lam[2]  = { tc_v(2), tc_v(3) };
    Term arr[2]  = { tc_v(2), tc_v(4) };
    Term t1[4]   = { tc_v(0), tc_v(1), tc_app(C_TM_LAM, lam), tc_app(C_TP_ARR, arr) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_PLAIN_WF, w0), SPACE_THM },
                         { tc_app(C_HAS_TYPE, t0), SPACE_THM } },
               .make = { tc_app(C_HAS_TYPE, t1), SPACE_THM } };
    R_TY_LAM = tc_rule(&r);
  }
  {
    /* R_TY_TLAM: keep HELPER_TPL_SHIFT1(d, tpl, d1, tpl1), HAS_TYPE(d1, tpl1, body, body_tp)
                  |- HAS_TYPE(d, tpl, TLam(body), TpAll(body_tp)) */
    Binder v[6] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(6, v);
    Term h0[4]  = { tc_v(0), tc_v(1), tc_v(2), tc_v(3) };
    Term t0[4]  = { tc_v(2), tc_v(3), tc_v(4), tc_v(5) };
    Term tl[1]  = { tc_v(4) };
    Term ta[1]  = { tc_v(5) };
    Term t1[4]  = { tc_v(0), tc_v(1), tc_app(C_TM_TLAM, tl), tc_app(C_TP_ALL, ta) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_HELPER_TPL_SHIFT1, h0), SPACE_HELPER },
                         { tc_app(C_HAS_TYPE, t0), SPACE_THM } },
               .make = { tc_app(C_HAS_TYPE, t1), SPACE_THM } };
    R_TY_TLAM = tc_rule(&r);
  }
  {
    /* R_TY_IMP: keep HAS_TYPE(d, tpl, p, Prop), HAS_TYPE(d, tpl, q, Prop) |- HAS_TYPE(d, tpl, Imp(p, q), Prop) */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term t0[4]  = { tc_v(0), tc_v(1), tc_v(2), T_TP_PROP };
    Term t1[4]  = { tc_v(0), tc_v(1), tc_v(3), T_TP_PROP };
    Term im[2]  = { tc_v(2), tc_v(3) };
    Term t2[4]  = { tc_v(0), tc_v(1), tc_app(C_TM_IMP, im), T_TP_PROP };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_HAS_TYPE, t0), SPACE_THM },
                         { tc_app(C_HAS_TYPE, t1), SPACE_THM } },
               .make = { tc_app(C_HAS_TYPE, t2), SPACE_THM } };
    R_TY_IMP = tc_rule(&r);
  }
  {
    /* R_TY_ALL: keep PLAIN_WF(d, dom), HAS_TYPE(d, TpLCons(dom, tpl), body, Prop) |- HAS_TYPE(d, tpl, All(dom, body), Prop) */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term w0[2]   = { tc_v(0), tc_v(2) };
    Term tplc[2] = { tc_v(2), tc_v(1) };
    Term t0[4]   = { tc_v(0), tc_app(C_TPLC, tplc), tc_v(3), T_TP_PROP };
    Term al[2]   = { tc_v(2), tc_v(3) };
    Term t1[4]   = { tc_v(0), tc_v(1), tc_app(C_TM_ALL, al), T_TP_PROP };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_PLAIN_WF, w0), SPACE_THM },
                         { tc_app(C_HAS_TYPE, t0), SPACE_THM } },
               .make = { tc_app(C_HAS_TYPE, t1), SPACE_THM } };
    R_TY_ALL = tc_rule(&r);
  }
  {
    /* R_PROP_BASE: keep HAS_TYPE(d, tpl, m, Prop) |- IS_PROP(d, tpl, m) */
    Binder v[3] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term t0[4] = { tc_v(0), tc_v(1), tc_v(2), T_TP_PROP };
    Term p0[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Rule r = { .nkeep = 1, .fresh = -1,
               .keep = { { tc_app(C_HAS_TYPE, t0), SPACE_THM } },
               .make = { tc_app(C_IS_PROP, p0), SPACE_THM } };
    R_PROP_BASE = tc_rule(&r);
  }
  {
    /* R_PROP_TALL: keep HELPER_TPL_SHIFT1(d, tpl, d1, TpLNil), IS_PROP(d1, TpLNil, body) |- IS_PROP(d, tpl, TAll(body)) */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term h0[4] = { tc_v(0), tc_v(1), tc_v(2), T_TPLN };
    Term p0[3] = { tc_v(2), T_TPLN, tc_v(3) };
    Term ta[1] = { tc_v(3) };
    Term p1[3] = { tc_v(0), tc_v(1), tc_app(C_TM_TALL, ta) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_HELPER_TPL_SHIFT1, h0), SPACE_HELPER },
                         { tc_app(C_IS_PROP, p0), SPACE_THM } },
               .make = { tc_app(C_IS_PROP, p1), SPACE_THM } };
    R_PROP_TALL = tc_rule(&r);
  }

  /* ---- 3. Signature declaration & theorem admission rules in SPACE_SIG / SPACE_THM ---- */
  {
    /* R_DECL_PARAM: keep PLAIN_WF(lv, body_tp)@SPACE_THM |- SIG_TERM(name, tp)@SPACE_SIG */
    Binder v[4] = {
      { (uint16_t)S_INT, 0, 0 },  { (uint16_t)S_TP, 0, 0 },
      { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(4, v);
    Term w0[2] = { tc_v(0), tc_v(1) };
    Term s0[2] = { tc_v(2), tc_v(3) };
    Rule r = { .nkeep = 1, .fresh = -1, .inputs = 0xC,   /* name, declared type */
               .keep = { { tc_app(C_PLAIN_WF, w0), SPACE_THM } },
               .make = { tc_app(C_SIG_TERM, s0), SPACE_SIG } };
    R_DECL_PARAM = tc_rule(&r);
  }
  {
    /* R_DECL_DEF: keep HAS_TYPE(0, TpLNil, body, tp)@SPACE_THM |- SIG_TERM(name, tp)@SPACE_SIG */
    Binder v[3] = {
      { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TP, 0, 0 }
    };
    tc_ctx(3, v);
    Term t0[4] = { mk_int(0), T_TPLN, tc_v(1), tc_v(2) };
    Term s0[2] = { tc_v(0), tc_v(2) };
    Rule r = { .nkeep = 1, .fresh = -1, .inputs = 0x1,   /* name */
               .keep = { { tc_app(C_HAS_TYPE, t0), SPACE_THM } },
               .make = { tc_app(C_SIG_TERM, s0), SPACE_SIG } };
    R_DECL_DEF = tc_rule(&r);
  }
  {
    /* R_DECL_AXIOM: keep IS_PROP(0, TpLNil, prop)@SPACE_THM
                     |- THM(Ctx(0, TpLNil, TmLNil), prop)@SPACE_THM + KNOWN_THM(name, prop)@SPACE_SIG */
    Binder v[2] = { { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 } };
    tc_ctx(2, v);
    Term p0[3] = { mk_int(0), T_TPLN, tc_v(1) };
    Term j0[2] = { T_CTX_EMPTY, tc_v(1) };
    Term k0[2] = { tc_v(0), tc_v(1) };
    Rule r = { .nkeep = 1, .nmake_extra = 1, .fresh = -1, .inputs = 0x1,   /* name */
               .keep = { { tc_app(C_IS_PROP, p0), SPACE_THM } },
               .make = { tc_app(C_THM, j0), SPACE_THM },
               .make_extra = { { tc_app(C_KNOWN_THM, k0), SPACE_SIG } } };
    R_DECL_AXIOM = tc_rule(&r);
  }
  {
    /* R_THM_IMPORT: keep IS_PROP(0, TpLNil, claim)@SPACE_THM, THM(T_CTX_EMPTY, inferred)@SPACE_THM,
                     HELPER_CONV(inferred, claim)@SPACE_HELPER
                     |- THM(T_CTX_EMPTY, claim)@SPACE_THM + KNOWN_THM(name, claim)@SPACE_SIG */
    Binder v[3] = {
      { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term p0[3] = { mk_int(0), T_TPLN, tc_v(1) };
    Term j0[2] = { T_CTX_EMPTY, tc_v(2) };
    Term c0[2] = { tc_v(2), tc_v(1) };
    Term j1[2] = { T_CTX_EMPTY, tc_v(1) };
    Term k0[2] = { tc_v(0), tc_v(1) };
    Rule r = { .nkeep = 3, .nmake_extra = 1, .fresh = -1, .inputs = 0x1,   /* name */
               .keep = { { tc_app(C_IS_PROP, p0), SPACE_THM },
                         { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_HELPER_CONV, c0), SPACE_HELPER } },
               .make = { tc_app(C_THM, j1), SPACE_THM },
               .make_extra = { { tc_app(C_KNOWN_THM, k0), SPACE_SIG } } };
    R_THM_IMPORT = tc_rule(&r);
  }

  /* ---- 4. The 8 Natural-Deduction Megalodon Proof Rules in SPACE_THM ---- */
  {
    /* 1. R_HYP: keep HELPER_TML_LOOKUP(tml, idx, h)@SPACE_HELPER |- THM(Ctx(d, tpl, tml), h)@SPACE_THM */
    Binder v[5] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(5, v);
    Term ha[3] = { tc_v(2), tc_v(3), tc_v(4) };
    Term cx[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term ja[2] = { tc_app(C_CTX, cx), tc_v(4) };
    Rule r = { .nkeep = 1, .fresh = -1, .inputs = 0x3,   /* depth, type list */
               .keep = { { tc_app(C_HELPER_TML_LOOKUP, ha), SPACE_HELPER } },
               .make = { tc_app(C_THM, ja), SPACE_THM } };
    R_HYP = tc_rule(&r);
  }
  {
    /* 2. R_KNOWN: keep KNOWN_THM(name, prop)@SPACE_SIG, THM(T_CTX_EMPTY, prop)@SPACE_THM |- THM(ctx, prop)@SPACE_THM */
    Binder v[3] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_NAME, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term ka[2] = { tc_v(1), tc_v(2) };
    Term j0[2] = { T_CTX_EMPTY, tc_v(2) };
    Term j1[2] = { tc_v(0), tc_v(2) };
    Rule r = { .nkeep = 2, .fresh = -1, .inputs = 0x1,   /* context */
               .keep = { { tc_app(C_KNOWN_THM, ka), SPACE_SIG },
                         { tc_app(C_THM, j0), SPACE_THM } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_KNOWN = tc_rule(&r);
  }
  {
    /* 3. R_TERM_APP: keep THM(Ctx(d, tpl, tml), qprop)@SPACE_THM,
                           HELPER_CONV(qprop, All(dom, body))@SPACE_HELPER,
                           HAS_TYPE(d, tpl, arg, dom)@SPACE_THM,
                           HELPER_TM_INST0(body, arg, concl)@SPACE_HELPER
                      |- THM(Ctx(d, tpl, tml), concl)@SPACE_THM */
    Binder v[8] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TP, 0, 0 },  { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(8, v);
    Term cx[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term ctx_t = tc_app(C_CTX, cx);
    Term j0[2] = { ctx_t, tc_v(3) };
    Term al[2] = { tc_v(4), tc_v(5) };
    Term c0[2] = { tc_v(3), tc_app(C_TM_ALL, al) };
    Term t0[4] = { tc_v(0), tc_v(1), tc_v(6), tc_v(4) };
    Term i0[3] = { tc_v(5), tc_v(6), tc_v(7) };
    Term j1[2] = { ctx_t, tc_v(7) };
    Rule r = { .nkeep = 4, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_HELPER_CONV, c0), SPACE_HELPER },
                         { tc_app(C_HAS_TYPE, t0), SPACE_THM },
                         { tc_app(C_HELPER_TM_INST0, i0), SPACE_HELPER } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TERM_APP = tc_rule(&r);
  }
  {
    /* 4. R_PROOF_APP: keep THM(ctx, iprop)@SPACE_THM, THM(ctx, aprop)@SPACE_THM,
                            HELPER_CONV(iprop, Imp(aprop, concl))@SPACE_HELPER
                       |- THM(ctx, concl)@SPACE_THM */
    Binder v[4] = {
      { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(4, v);
    Term j0[2] = { tc_v(0), tc_v(1) };
    Term j1[2] = { tc_v(0), tc_v(2) };
    Term im[2] = { tc_v(2), tc_v(3) };
    Term c0[2] = { tc_v(1), tc_app(C_TM_IMP, im) };
    Term j2[2] = { tc_v(0), tc_v(3) };
    Rule r = { .nkeep = 3, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_THM, j1), SPACE_THM },
                         { tc_app(C_HELPER_CONV, c0), SPACE_HELPER } },
               .make = { tc_app(C_THM, j2), SPACE_THM } };
    R_PROOF_APP = tc_rule(&r);
  }
  {
    /* 5. R_TERM_LAM: keep PLAIN_WF(d, tp)@SPACE_THM, HELPER_TML_SHIFT1(tml, tml1)@SPACE_HELPER,
                           THM(Ctx(d, TpLCons(tp, tpl), tml1), body)@SPACE_THM
                      |- THM(Ctx(d, tpl, tml), All(tp, body))@SPACE_THM */
    Binder v[6] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_TP, 0, 0 },
      { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(6, v);
    Term w0[2]   = { tc_v(0), tc_v(3) };
    Term s0[2]   = { tc_v(2), tc_v(4) };
    Term tplc[2] = { tc_v(3), tc_v(1) };
    Term icx[3]  = { tc_v(0), tc_app(C_TPLC, tplc), tc_v(4) };
    Term j0[2]   = { tc_app(C_CTX, icx), tc_v(5) };
    Term ocx[3]  = { tc_v(0), tc_v(1), tc_v(2) };
    Term al[2]   = { tc_v(3), tc_v(5) };
    Term j1[2]   = { tc_app(C_CTX, ocx), tc_app(C_TM_ALL, al) };
    Rule r = { .nkeep = 3, .fresh = -1,
               .keep = { { tc_app(C_PLAIN_WF, w0), SPACE_THM },
                         { tc_app(C_HELPER_TML_SHIFT1, s0), SPACE_HELPER },
                         { tc_app(C_THM, j0), SPACE_THM } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TERM_LAM = tc_rule(&r);
  }
  {
    /* 6. R_PROOF_LAM: keep HAS_TYPE(d, tpl, src, Prop)@SPACE_THM,
                            THM(Ctx(d, tpl, TmLCons(src, tml)), body)@SPACE_THM
                       |- THM(Ctx(d, tpl, tml), Imp(src, body))@SPACE_THM */
    Binder v[5] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_TM, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(5, v);
    Term t0[4]   = { tc_v(0), tc_v(1), tc_v(3), T_TP_PROP };
    Term tmlc[2] = { tc_v(3), tc_v(2) };
    Term icx[3]  = { tc_v(0), tc_v(1), tc_app(C_TMLC, tmlc) };
    Term j0[2]   = { tc_app(C_CTX, icx), tc_v(4) };
    Term ocx[3]  = { tc_v(0), tc_v(1), tc_v(2) };
    Term im[2]   = { tc_v(3), tc_v(4) };
    Term j1[2]   = { tc_app(C_CTX, ocx), tc_app(C_TM_IMP, im) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_HAS_TYPE, t0), SPACE_THM },
                         { tc_app(C_THM, j0), SPACE_THM } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_PROOF_LAM = tc_rule(&r);
  }
  {
    /* 7. R_TYPE_APP: keep THM(Ctx(d, tpl, tml), qprop)@SPACE_THM,
                           HELPER_CONV(qprop, TAll(body))@SPACE_HELPER,
                           PLAIN_WF(d, tp)@SPACE_THM,
                           HELPER_TINST0(body, tp, concl)@SPACE_HELPER
                      |- THM(Ctx(d, tpl, tml), concl)@SPACE_THM */
    Binder v[7] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TPL, 0, 0 },
      { (uint16_t)S_TML, 0, 0 }, { (uint16_t)S_TM, 0, 0 },
      { (uint16_t)S_TM, 0, 0 },  { (uint16_t)S_TP, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(7, v);
    Term cx[3] = { tc_v(0), tc_v(1), tc_v(2) };
    Term ctx_t = tc_app(C_CTX, cx);
    Term j0[2] = { ctx_t, tc_v(3) };
    Term ta[1] = { tc_v(4) };
    Term c0[2] = { tc_v(3), tc_app(C_TM_TALL, ta) };
    Term w0[2] = { tc_v(0), tc_v(5) };
    Term i0[3] = { tc_v(4), tc_v(5), tc_v(6) };
    Term j1[2] = { ctx_t, tc_v(6) };
    Rule r = { .nkeep = 4, .fresh = -1,
               .keep = { { tc_app(C_THM, j0), SPACE_THM },
                         { tc_app(C_HELPER_CONV, c0), SPACE_HELPER },
                         { tc_app(C_PLAIN_WF, w0), SPACE_THM },
                         { tc_app(C_HELPER_TINST0, i0), SPACE_HELPER } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TYPE_APP = tc_rule(&r);
  }
  {
    /* 8. R_TYPE_LAM: keep HELPER_TPL_SHIFT1(d, TpLNil, d1, TpLNil)@SPACE_HELPER,
                           THM(Ctx(d1, TpLNil, TmLNil), body)@SPACE_THM
                      |- THM(Ctx(d, TpLNil, TmLNil), TAll(body))@SPACE_THM */
    Binder v[3] = {
      { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_INT, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term s0[4]  = { tc_v(0), T_TPLN, tc_v(1), T_TPLN };
    Term icx[3] = { tc_v(1), T_TPLN, T_TMLN };
    Term j0[2]  = { tc_app(C_CTX, icx), tc_v(2) };
    Term ocx[3] = { tc_v(0), T_TPLN, T_TMLN };
    Term ta[1]  = { tc_v(2) };
    Term j1[2]  = { tc_app(C_CTX, ocx), tc_app(C_TM_TALL, ta) };
    Rule r = { .nkeep = 2, .fresh = -1,
               .keep = { { tc_app(C_HELPER_TPL_SHIFT1, s0), SPACE_HELPER },
                         { tc_app(C_THM, j0), SPACE_THM } },
               .make = { tc_app(C_THM, j1), SPACE_THM } };
    R_TYPE_LAM = tc_rule(&r);
  }

  /* ---- 5. Subproof Space Birth + Reach (NamedSpaces, SpacesCreation, NamedSpacesReach) ---- */
  {
    Binder v[3] = {
      { sp_sort, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term s = tc_v(0), ctx = tc_v(1), h = tc_v(2);
    Term sa[1] = { s };
    Term ha[2] = { ctx, h };
    Rule r = {
      .nkeep = 1, .nmake_extra = 2, .birth_law = 1, .fresh = -1,
      .keep = { { tc_app(C_SUB_AUTH, ha), SPACE_HELPER } },
      .make = { tc_app(C_HANDLE, sa), SPACE_HELPER },
      .make_extra = {
        { tc_at_birth(s, tc_app(C_SUB_MARK, sa)), 0 },
        { tc_at_space(s, tc_app(C_SUB_HYP, ha)), 0 }
      }
    };
    R_SUB_BIRTH = tc_rule(&r);
  }
  {
    Binder v[3] = {
      { sp_sort, 0, 0 }, { (uint16_t)S_CTX, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(3, v);
    Term s = tc_v(0), ctx = tc_v(1), h = tc_v(2);
    Term ha[2] = { ctx, h };
    Rule r = {
      .birth_law = 1, .nkeep = 1, .fresh = -1,
      .keep = { { tc_at_space(s, tc_app(C_SUB_HYP, ha)), 0 } },
      .make = { tc_app(C_THM, ha), SPACE_THM }
    };
    R_SUB_USE_HYP = tc_rule(&r);
  }
  {
    /* 6. Bodhisattva Runtime Capability & Proof-Carrying Gate (R_ACT_GATE):
          take ACT_REQ(act_prop)@s, keep THM(T_CTX_EMPTY, act_prop)@SPACE_THM
          |- ACT_COMMIT(act_prop)@s  (under birth_law + tc_fire_reach) */
    Binder v[2] = {
      { sp_sort, 0, 0 }, { (uint16_t)S_TM, 0, 0 }
    };
    tc_ctx(2, v);
    Term s = tc_v(0), act_prop = tc_v(1);
    Term req_a[1] = { act_prop };
    Term thm_a[2] = { T_CTX_EMPTY, act_prop };
    Rule r = {
      .birth_law = 1, .ntake = 1, .nkeep = 1, .fresh = -1,
      .take = { { tc_at_space(s, tc_app(C_ACT_REQ, req_a)), 0 } },
      .keep = { { tc_app(C_THM, thm_a), SPACE_THM } },
      .make = { tc_at_space(s, tc_app(C_ACT_COMMIT, req_a)), 0 }
    };
    R_ACT_GATE = tc_rule(&r);
  }

  /* Post birth markers for static spaces so birth_law rules can read/write them */
  Term sp_sig = tc_space_term(SPACE_SIG);
  Term sp_thm = tc_space_term(SPACE_THM);
  Term sp_hlp = tc_space_term(SPACE_HELPER);
  Term m_sig[1] = { sp_sig }, m_thm[1] = { sp_thm }, m_hlp[1] = { sp_hlp };
  tc_post_at(sp_sig, tc_app(C_SUB_MARK, m_sig), true);
  tc_post_at(sp_thm, tc_app(C_SUB_MARK, m_thm), true);
  tc_post_at(sp_hlp, tc_app(C_SUB_MARK, m_hlp), true);

  tc_protect(SPACE_SIG);
  tc_protect(SPACE_THM);
  tc_seal();
}

/* ---- S-expression parser for -sexprinfo files ---- */
enum { SX_ATOM = 1, SX_STR, SX_INT, SX_LIST };
typedef struct Sx {
  uint8_t kind;
  uint32_t len;
  uint64_t val;
  const char *text; /* points into file buffer (null-terminated in place) */
  struct Sx **items;
} Sx;

typedef struct SxChunk {
  struct SxChunk *next;
  size_t used;
  Sx nodes[8192];
} SxChunk;

typedef struct PtrChunk {
  struct PtrChunk *next;
  size_t used;
  Sx *ptrs[32768];
} PtrChunk;

static SxChunk *sx_chunks;
static PtrChunk *ptr_chunks;

static Sx *alloc_sx(uint8_t kind) {
  if (!sx_chunks || sx_chunks->used == 8192) {
    SxChunk *c = calloc(1, sizeof(SxChunk));
    c->next = sx_chunks;
    sx_chunks = c;
  }
  Sx *s = &sx_chunks->nodes[sx_chunks->used++];
  s->kind = kind;
  return s;
}

static Sx **alloc_ptrs(uint32_t n) {
  if (!n) return NULL;
  if (n > 32768) return malloc((size_t)n * sizeof(Sx *));
  if (!ptr_chunks || ptr_chunks->used + n > 32768) {
    PtrChunk *c = calloc(1, sizeof(PtrChunk));
    c->next = ptr_chunks;
    ptr_chunks = c;
  }
  Sx **p = &ptr_chunks->ptrs[ptr_chunks->used];
  ptr_chunks->used += n;
  return p;
}

static void free_sx_arena(void) {
  while (sx_chunks) {
    SxChunk *n = sx_chunks->next;
    free(sx_chunks);
    sx_chunks = n;
  }
  while (ptr_chunks) {
    PtrChunk *n = ptr_chunks->next;
    free(ptr_chunks);
    ptr_chunks = n;
  }
}

static void skip_ws(char **p) {
  char *s = *p;
#ifdef TC_USE_CESTA_EXPORT
  if (g_sx_buf_end && s <= g_sx_buf_end) {
    size_t rem = (size_t)(g_sx_buf_end - s);
    size_t adv = tc_scanner_skip_sexpr_ws((cesta_read_bytes){ (const uint8_t *)s, rem }, 0);
    *p = s + adv;
    return;
  }
#endif
  for (;;) {
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s == ';') {
      while (*s && *s != '\n') s++;
      continue;
    }
    break;
  }
  *p = s;
}

static Sx *parse_sx(char **p) {
  skip_ws(p);
  char *s = *p;
  if (!*s) return NULL;
  if (*s == '(') {
    s++;
    *p = s;
    Sx *tmp[256];
    Sx **dyn = NULL;
    uint32_t len = 0, cap = 256;
    for (;;) {
      skip_ws(p);
      if (!**p) { free(dyn); return NULL; }
      if (**p == ')') { (*p)++; break; }
      Sx *it = parse_sx(p);
      if (!it) { free(dyn); return NULL; }
      if (len == cap) {
        uint32_t nc = cap * 2;
        Sx **nd = malloc((size_t)nc * sizeof(Sx *));
        memcpy(nd, dyn ? dyn : tmp, (size_t)len * sizeof(Sx *));
        free(dyn);
        dyn = nd;
        cap = nc;
      }
      if (dyn) dyn[len++] = it;
      else tmp[len++] = it;
    }
    Sx *l = alloc_sx(SX_LIST);
    l->len = len;
    if (dyn) {
      l->items = dyn;
    } else {
      l->items = alloc_ptrs(len);
      if (len) memcpy(l->items, tmp, (size_t)len * sizeof(Sx *));
    }
    return l;
  }
  if (*s == '"') {
    s++;
    char *start = s, *w = s;
    while (*s && *s != '"') {
      if (*s == '\\' && s[1]) s++;
      *w++ = *s++;
    }
    if (*s == '"') s++;
    *w = '\0';
    *p = s;
    Sx *st = alloc_sx(SX_STR);
    st->text = start;
    st->len = (uint32_t)(w - start);
    return st;
  }
  char *start = s;
#ifdef TC_USE_CESTA_EXPORT
  if (g_sx_buf_end && s <= g_sx_buf_end) {
    size_t rem = (size_t)(g_sx_buf_end - s);
    s += tc_scanner_scan_sexpr_atom_len((cesta_read_bytes){ (const uint8_t *)s, rem }, 0);
  } else
#endif
  while (*s && !isspace((unsigned char)*s) && *s != '(' && *s != ')' && *s != '"')
    s++;
  size_t len = (size_t)(s - start);
  bool all_digits = len > 0;
  uint64_t val = 0;
  for (size_t i = 0; i < len; i++) {
    if (start[i] < '0' || start[i] > '9') { all_digits = false; break; }
    uint64_t digit = (uint64_t)(start[i] - '0');
    if (val > (UINT64_MAX - digit) / 10u) return NULL;   /* does not fit in 64 bits */
    val = val * 10u + digit;
  }
  if (all_digits && val > g_sx_int_max) return NULL;     /* no index or count is that large */
  if (*s == ')' || *s == '(') {
    /* copy short atom or move? We can overwrite only if we save char, or we can
       check if we only need strncmp for atoms! Wait: for SX_ATOM we only ever
       compare against literal strings, so st->text + st->len is enough! */
  }
  *p = s;
  if (all_digits) {
    Sx *in = alloc_sx(SX_INT);
    in->val = val;
    return in;
  }
  Sx *at = alloc_sx(SX_ATOM);
  at->text = start;
  at->len = (uint32_t)len;
  return at;
}

static inline bool sx_is_atom(const Sx *x, const char *lit) {
  size_t n = strlen(lit);
  return x && x->kind == SX_ATOM && x->len == n && memcmp(x->text, lit, n) == 0;
}

/* ---- Decoding upstream types, terms, and proofs ---- */
static Term decode_tp(const Sx *x, uint32_t levels) {
  if (!x || x->kind != SX_LIST || x->len == 0) return 0;
  if (x->len == 1 && sx_is_atom(x->items[0], "PROP")) return mk_tp_prop();
  if (x->len == 1 && sx_is_atom(x->items[0], "SET")) return mk_tp_base(0);
  if (x->len == 2 && sx_is_atom(x->items[0], "TPVAR") && x->items[1]->kind == SX_INT) {
    uint64_t i = x->items[1]->val;
    return i < levels ? mk_tp_var(levels - (uint32_t)i - 1u) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "AR")) {
    Term a = decode_tp(x->items[1], levels);
    Term b = a ? decode_tp(x->items[2], levels) : 0;
    return b ? mk_tp_arr(a, b) : 0;
  }
  return 0;
}

static Term wrap_poly_tp(Term body, uint32_t levels) {
  for (uint32_t i = 0; body && i < levels; i++) body = mk_tp_all(body);
  return body;
}

static Term decode_tm(const Sx *x, uint32_t levels) {
  if (!x || x->kind != SX_LIST || x->len == 0) return 0;
  if (x->len == 2 && sx_is_atom(x->items[0], "DB") && x->items[1]->kind == SX_INT)
    return mk_tm_db((uint32_t)x->items[1]->val);
  if (x->len == 2 && sx_is_atom(x->items[0], "TMH") && x->items[1]->kind == SX_STR)
    return mk_tm_name(sym_intern_n(x->items[1]->text, x->items[1]->len));
  if (x->len == 2 && sx_is_atom(x->items[0], "PRIM") && x->items[1]->kind == SX_INT)
    return mk_tm_prim((uint32_t)x->items[1]->val);
  if (x->len == 3 && sx_is_atom(x->items[0], "TPAP")) {
    Term f = decode_tm(x->items[1], levels);
    Term a = f ? decode_tp(x->items[2], levels) : 0;
    return a ? mk_tm_tap(f, a) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "AP")) {
    Term f = decode_tm(x->items[1], levels);
    Term a = f ? decode_tm(x->items[2], levels) : 0;
    return a ? mk_tm_ap(f, a) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "LAM")) {
    Term a = decode_tp(x->items[1], levels);
    Term b = a ? decode_tm(x->items[2], levels) : 0;
    return b ? mk_tm_lam(a, b) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "IMP")) {
    Term a = decode_tm(x->items[1], levels);
    Term b = a ? decode_tm(x->items[2], levels) : 0;
    return b ? mk_tm_imp(a, b) : 0;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "ALL")) {
    Term a = decode_tp(x->items[1], levels);
    Term b = a ? decode_tm(x->items[2], levels) : 0;
    return b ? mk_tm_all(a, b) : 0;
  }
  return 0;
}

static Term wrap_poly_tm(Term body, uint32_t levels, bool is_lam) {
  for (uint32_t i = 0; body && i < levels; i++)
    body = is_lam ? mk_tm_tlam(body) : mk_tm_tall(body);
  return body;
}

static MgPf *decode_pf(const Sx *x, uint32_t levels) {
  if (!x || x->kind != SX_LIST || x->len == 0) return NULL;
  if (x->len == 2 && sx_is_atom(x->items[0], "HYP") && x->items[1]->kind == SX_INT) {
    MgPf *p = alloc_pf(PF_HYP);
    p->n = (uint32_t)x->items[1]->val;
    return p;
  }
  if (x->len == 2 && sx_is_atom(x->items[0], "KNOWN") && x->items[1]->kind == SX_STR) {
    MgPf *p = alloc_pf(PF_KNOWN);
    p->n = sym_intern_n(x->items[1]->text, x->items[1]->len);
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PTPAP")) {
    MgPf *d = decode_pf(x->items[1], levels);
    Term a = d ? decode_tp(x->items[2], levels) : 0;
    if (!a) return NULL;
    MgPf *p = alloc_pf(PF_TPAP);
    p->p = d; p->tp = a;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PTMAP")) {
    MgPf *d = decode_pf(x->items[1], levels);
    Term a = d ? decode_tm(x->items[2], levels) : 0;
    if (!a) return NULL;
    MgPf *p = alloc_pf(PF_TMAP);
    p->p = d; p->t = a;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PPFAP")) {
    MgPf *d1 = decode_pf(x->items[1], levels);
    MgPf *d2 = d1 ? decode_pf(x->items[2], levels) : NULL;
    if (!d2) return NULL;
    MgPf *p = alloc_pf(PF_PFAP);
    p->p = d1; p->q = d2;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "PLAM")) {
    Term s = decode_tm(x->items[1], levels);
    MgPf *d = s ? decode_pf(x->items[2], levels) : NULL;
    if (!d) return NULL;
    MgPf *p = alloc_pf(PF_PLAM);
    p->t = s; p->p = d;
    return p;
  }
  if (x->len == 3 && sx_is_atom(x->items[0], "TLAM")) {
    Term a = decode_tp(x->items[1], levels);
    MgPf *d = a ? decode_pf(x->items[2], levels) : NULL;
    if (!d) return NULL;
    MgPf *p = alloc_pf(PF_TLAM);
    p->tp = a; p->p = d;
    return p;
  }
  return NULL;
}

static MgPf *wrap_poly_pf(MgPf *pf, uint32_t levels) {
  for (uint32_t i = 0; pf && i < levels; i++) {
    MgPf *w = alloc_pf(PF_TPLAM);
    w->p = pf;
    pf = w;
  }
  return pf;
}

/* ---- Replay a Megalodon -sexprinfo file (and optional --emit-dk translator) ---- */
typedef struct {
  uint32_t prims, params, defs, axioms, thms, repeated;
} ReplayStats;

enum {
  DK_ITEM_PRIM = 1, DK_ITEM_PARAM, DK_ITEM_DEF, DK_ITEM_AXIOM, DK_ITEM_THM
};
typedef struct {
  uint8_t  kind;
  uint32_t sym;
  uint32_t prim_idx;
  uint32_t thm_seq;
  Term     tp;   /* or prop for AXIOM/THM */
  Term     body; /* for DEF */
  MgPf    *pf;   /* for THM */
} DkEmitItem;

static const char *g_emit_dk_path = NULL;
static DkEmitItem *dk_items = NULL;
static size_t dk_items_len = 0, dk_items_cap = 0;
static uint32_t dk_thm_seq = 0;

static void push_dk_item(DkEmitItem it) {
  if (!g_emit_dk_path) return;
  if (dk_items_len >= dk_items_cap) {
    size_t nc = dk_items_cap ? dk_items_cap * 2 : 1024;
    dk_items = realloc(dk_items, nc * sizeof(DkEmitItem));
    dk_items_cap = nc;
  }
  dk_items[dk_items_len++] = it;
}

static void dk_print_tp(FILE *out, Term tp, uint32_t tv_depth) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TP_PROP) {
    fputs("bool", out);
  } else if (hc == C_TP_BASE) {
    fputs("set", out);
  } else if (hc == C_TP_VAR) {
    uint32_t idx = int_val(a[0]);
    if (idx < tv_depth) fprintf(out, "a%u", tv_depth - 1u - idx);
    else fprintf(out, "a_oob_%u", idx);
  } else if (hc == C_TP_ARR) {
    fputs("(arr ", out);
    dk_print_tp(out, a[0], tv_depth);
    fputc(' ', out);
    dk_print_tp(out, a[1], tv_depth);
    fputc(')', out);
  } else {
    fputs("bool", out);
  }
}

static void dk_print_poly_tp(FILE *out, Term tp, uint32_t tv_depth) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(tp, &k, &h, &ar, &a);
  if ((int)h == C_TP_ALL) {
    fprintf(out, "(forallK (a%u : type => ", tv_depth);
    dk_print_poly_tp(out, a[0], tv_depth + 1u);
    fputs("))", out);
  } else {
    fputs("(p ", out);
    dk_print_tp(out, tp, tv_depth);
    fputc(')', out);
  }
}

static void dk_print_tm(FILE *out, Term m, uint32_t tv_depth, uint32_t tm_depth) {
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(m, &k, &h, &ar, &a);
  int hc = (int)h;
  if (hc == C_TM_DB) {
    uint32_t idx = int_val(a[0]);
    if (idx < tm_depth) fprintf(out, "x%u", tm_depth - 1u - idx);
    else fprintf(out, "x_oob_%u", idx);
  } else if (hc == C_TM_NAME) {
    uint32_t id = meta_of(a[0])->uval;
    fprintf(out, "tm_%s", syms[id].text);
  } else if (hc == C_TM_PRIM) {
    fprintf(out, "prim_%u", int_val(a[0]));
  } else if (hc == C_TM_TAP) {
    fputc('(', out);
    dk_print_tm(out, a[0], tv_depth, tm_depth);
    fputc(' ', out);
    dk_print_tp(out, a[1], tv_depth);
    fputc(')', out);
  } else if (hc == C_TM_AP) {
    fputc('(', out);
    dk_print_tm(out, a[0], tv_depth, tm_depth);
    fputc(' ', out);
    dk_print_tm(out, a[1], tv_depth, tm_depth);
    fputc(')', out);
  } else if (hc == C_TM_LAM) {
    fprintf(out, "(x%u : eta ", tm_depth);
    dk_print_tp(out, a[0], tv_depth);
    fputs(" => ", out);
    dk_print_tm(out, a[1], tv_depth, tm_depth + 1u);
    fputc(')', out);
  } else if (hc == C_TM_TLAM) {
    fprintf(out, "(a%u : type => ", tv_depth);
    dk_print_tm(out, a[0], tv_depth + 1u, tm_depth);
    fputc(')', out);
  } else if (hc == C_TM_IMP) {
    fputs("(impl ", out);
    dk_print_tm(out, a[0], tv_depth, tm_depth);
    fputc(' ', out);
    dk_print_tm(out, a[1], tv_depth, tm_depth);
    fputc(')', out);
  } else if (hc == C_TM_ALL) {
    fputs("(forall ", out);
    dk_print_tp(out, a[0], tv_depth);
    fprintf(out, " (x%u : eta ", tm_depth);
    dk_print_tp(out, a[0], tv_depth);
    fputs(" => ", out);
    dk_print_tm(out, a[1], tv_depth, tm_depth + 1u);
    fputs("))", out);
  } else if (hc == C_TM_TALL) {
    fprintf(out, "(forallP (a%u : type => ", tv_depth);
    dk_print_tm(out, a[0], tv_depth + 1u, tm_depth);
    fputs("))", out);
  }
}

static void dk_print_pf(FILE *out, const MgPf *pf, uint32_t tv_depth, uint32_t tm_depth, uint32_t pf_depth) {
  if (!pf) { fputs("pf_null", out); return; }
  switch (pf->tag) {
  case PF_HYP:
    if (pf->n < pf_depth) fprintf(out, "H%u", pf_depth - 1u - pf->n);
    else fprintf(out, "H_oob_%u", pf->n);
    break;
  case PF_KNOWN:
    fprintf(out, "kn_%s", syms[pf->n].text);
    break;
  case PF_TPAP:
    fputc('(', out);
    dk_print_pf(out, pf->p, tv_depth, tm_depth, pf_depth);
    fputc(' ', out);
    dk_print_tp(out, pf->tp, tv_depth);
    fputc(')', out);
    break;
  case PF_TMAP:
    fputc('(', out);
    dk_print_pf(out, pf->p, tv_depth, tm_depth, pf_depth);
    fputc(' ', out);
    dk_print_tm(out, tm_nf(pf->t), tv_depth, tm_depth);
    fputc(')', out);
    break;
  case PF_PFAP:
    fputc('(', out);
    dk_print_pf(out, pf->p, tv_depth, tm_depth, pf_depth);
    fputc(' ', out);
    dk_print_pf(out, pf->q, tv_depth, tm_depth, pf_depth);
    fputc(')', out);
    break;
  case PF_PLAM:
    fprintf(out, "(H%u : eps ", pf_depth);
    dk_print_tm(out, tm_nf(pf->t), tv_depth, tm_depth);
    fputs(" => ", out);
    dk_print_pf(out, pf->p, tv_depth, tm_depth, pf_depth + 1u);
    fputc(')', out);
    break;
  case PF_TLAM:
    fprintf(out, "(x%u : eta ", tm_depth);
    dk_print_tp(out, pf->tp, tv_depth);
    fputs(" => ", out);
    dk_print_pf(out, pf->p, tv_depth, tm_depth + 1u, pf_depth);
    fputc(')', out);
    break;
  case PF_TPLAM:
    fprintf(out, "(a%u : type => ", tv_depth);
    dk_print_pf(out, pf->p, tv_depth + 1u, tm_depth, pf_depth);
    fputc(')', out);
    break;
  default:
    fputs("pf_gpa", out);
    break;
  }
}

static bool emit_dk_file(const char *dk_path, bool replay_ok) {
  FILE *out = fopen(dk_path, "wb");
  if (!out) {
    fprintf(stderr, "mg_tcalc: cannot open %s for --emit-dk\n", dk_path);
    return false;
  }
  fputs("(; Generated by mg_tcalc --emit-dk (4-Level Tower: tcalc -> Dedukti -> STTfa -> HOTG) ;)\n"
        "type : Type.\n"
        "arr : type -> type -> type.\n"
        "bool : type.\n"
        "set : type.\n\n"
        "def eta : type -> Type.\n"
        "ptype : Type.\n"
        "p : type -> ptype.\n"
        "def etap : ptype -> Type.\n"
        "forallK : (type -> ptype) -> ptype.\n"
        "def eps : eta bool -> Type.\n"
        "impl : eta bool -> eta bool -> eta bool.\n"
        "forall : t : type -> (eta t -> eta bool) -> eta bool.\n"
        "forallP : (type -> eta bool) -> eta bool.\n\n"
        "[] eta --> t : type => etap (p t).\n"
        "[l : type, r : type] etap (p (arr l r)) --> eta l -> eta r.\n"
        "[f : type -> ptype] etap (forallK f) --> x : type -> etap (f x).\n"
        "[t : type, f : eta t -> eta bool] eps (forall t f) --> x : eta t -> eps (f x).\n"
        "[l : eta bool, r : eta bool] eps (impl l r) --> eps l -> eps r.\n"
        "[f : type -> eta bool] eps (forallP f) --> x : type -> eps (f x).\n\n", out);
  for (uint32_t j = 0; j < nprims; j++) {
    if (prim_types[j]) {
      fprintf(out, "prim_%u : etap ", j);
      dk_print_poly_tp(out, prim_types[j], 0);
      fputs(".\n", out);
    }
  }
  fputc('\n', out);
  for (size_t i = 0; i < dk_items_len; i++) {
    const DkEmitItem *it = &dk_items[i];
    uint32_t h = it->sym;
    if (it->kind == DK_ITEM_PRIM) {
      if (syms[h].dk_emitted_tm) continue;
      syms[h].dk_emitted_tm = true;
      fprintf(out, "def tm_%s : etap ", syms[h].text);
      dk_print_poly_tp(out, it->tp, 0);
      fprintf(out, " := prim_%u.\n", it->prim_idx);
    } else if (it->kind == DK_ITEM_PARAM) {
      if (syms[h].dk_emitted_tm) continue;
      syms[h].dk_emitted_tm = true;
      fprintf(out, "tm_%s : etap ", syms[h].text);
      dk_print_poly_tp(out, it->tp, 0);
      fputs(".\n", out);
    } else if (it->kind == DK_ITEM_DEF) {
      if (syms[h].dk_emitted_tm) continue;
      syms[h].dk_emitted_tm = true;
      bool make_transparent = syms[h].unfolded || !replay_ok;
      fprintf(out, "%s tm_%s : etap ", make_transparent ? "def" : "thm", syms[h].text);
      dk_print_poly_tp(out, it->tp, 0);
      fputs(" := ", out);
      dk_print_tm(out, it->body, 0, 0);
      fputs(".\n", out);
    } else if (it->kind == DK_ITEM_AXIOM) {
      if (syms[h].dk_emitted_kn) continue;
      syms[h].dk_emitted_kn = true;
      fprintf(out, "kn_%s : eps ", syms[h].text);
      dk_print_tm(out, it->tp, 0, 0);
      fputs(".\n", out);
    } else if (it->kind == DK_ITEM_THM) {
      if (!syms[h].dk_emitted_kn) {
        syms[h].dk_emitted_kn = true;
        fprintf(out, "thm kn_%s : eps ", syms[h].text);
      } else {
        fprintf(out, "thm thm_dup_%u_%s : eps ", it->thm_seq, syms[h].text);
      }
      dk_print_tm(out, it->tp, 0, 0);
      fputs(" := ", out);
      dk_print_pf(out, it->pf, 0, 0, 0);
      fputs(".\n", out);
    }
  }
  fclose(out);
  return true;
}

static bool replay_sexpr_file(const char *path, ReplayStats *st) {
  FILE *f = fopen(path, "rb");
  if (!f) { fprintf(stderr, "mg_tcalc: cannot open %s\n", path); return false; }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (sz < 0) { fclose(f); return false; }
  char *buf = got(malloc((size_t)sz + 1), "source text");
  if ((long)fread(buf, 1, (size_t)sz, f) != sz) {
    fclose(f); free(buf); return false;
  }
  fclose(f);
  buf[sz] = '\0';
  g_sx_int_max = (uint64_t)sz < (uint64_t)INT32_MAX ? (uint64_t)sz : (uint64_t)INT32_MAX;
#ifdef TC_USE_CESTA_EXPORT
  g_sx_buf_end = buf + sz;
#endif

  dk_items_len = 0;
  dk_thm_seq = 0;
  char *cur = buf;
  bool ok = true;
  bool pending = false;
  bool pending_proved = false;
  uint32_t pending_sym = 0, pending_levels = 0;
  Term pending_prop = 0;
  Occ  pending_prop_occ = 0;
  const char *pending_name = "";

  while (ok) {
    skip_ws(&cur);
    if (!*cur) break;
    Sx *x = parse_sx(&cur);
    if (!x || x->kind != SX_LIST || x->len == 0) {
      fprintf(stderr, "mg_tcalc: malformed top-level S-expression in %s\n", path);
      ok = false; break;
    }
    const Sx *hd = x->items[0];
    if (sx_is_atom(hd, "PRIM") && x->len == 6) {
      uint32_t j = (uint32_t)x->items[1]->val;
      const char *name = x->items[2]->text;
      uint32_t h = sym_intern_n(x->items[3]->text, x->items[3]->len);
      if (j >= nprims || !prim_types[j]) {
        fprintf(stderr, "mg_tcalc: PRIM %s index %u out of range\n", name, j);
        ok = false; break;
      }
      uint32_t lv = 0;
      for (Term t = prim_types[j];;) {
        uint8_t tk; uint32_t th; int tar; const Term *ta;
        tc_node(t, &tk, &th, &tar, &ta);
        if ((int)th != C_TP_ALL) break;
        t = ta[0]; lv++;
      }
      Term tp = wrap_poly_tp(decode_tp(x->items[4], lv), lv);
      if (tp != prim_types[j]) {
        fprintf(stderr, "mg_tcalc: PRIM %s type mismatch\n", name);
        ok = false; break;
      }
      Term body = mk_tm_prim(j);
      if (syms[h].has_term) {
        if (syms[h].tp == tp && syms[h].def == body) { st->repeated++; }
        else { ok = false; break; }
      } else {
        Term inf_tp = 0;
        Occ oty = prove_has_type(0, T_TPLN, body, &inf_tp);
        if (!oty || inf_tp != tp) { ok = false; break; }
        Occ keep[1] = { oty };
        Term inst[3] = { syms[h].nterm, body, tp };
        Occ socc = commit_mg_step(R_DECL_DEF, keep, inst);
        if (!socc) { ok = false; break; }
        syms[h].has_term = true;
        syms[h].tp = tp;
        syms[h].def = body;
        syms[h].sig_occ = socc;
        syms[h].term_seq = next_decl_seq++;
        st->prims++;
        push_dk_item((DkEmitItem){ .kind = DK_ITEM_PRIM, .sym = h, .prim_idx = j, .tp = tp });
      }
    } else if (sx_is_atom(hd, "PARAM") && x->len == 6) {
      const char *name = x->items[1]->text;
      uint32_t h = sym_intern_n(x->items[2]->text, x->items[2]->len);
      uint32_t lv = (uint32_t)x->items[3]->val;
      Term body_tp = decode_tp(x->items[4], lv);
      Occ owf = body_tp ? prove_plain_wf(lv, body_tp) : 0;
      if (!owf) {
        fprintf(stderr, "mg_tcalc: PARAM %s ill-formed type\n", name);
        ok = false; break;
      }
      Term tp = wrap_poly_tp(body_tp, lv);
      if (syms[h].has_term) {
        if (syms[h].tp == tp) st->repeated++;
        else { ok = false; break; }
      } else {
        Occ keep[1] = { owf };
        Term inst[4] = { mk_int(lv), body_tp, syms[h].nterm, tp };
        Occ socc = commit_mg_step(R_DECL_PARAM, keep, inst);
        if (!socc) { ok = false; break; }
        syms[h].has_term = true;
        syms[h].is_param = true;
        syms[h].tp = tp;
        syms[h].def = 0;
        syms[h].sig_occ = socc;
        syms[h].term_seq = next_decl_seq++;
        st->params++;
        push_dk_item((DkEmitItem){ .kind = DK_ITEM_PARAM, .sym = h, .tp = tp });
      }
    } else if (sx_is_atom(hd, "DEF") && x->len == 7) {
      const char *name = x->items[1]->text;
      uint32_t h = sym_intern_n(x->items[2]->text, x->items[2]->len);
      uint32_t lv = (uint32_t)x->items[3]->val;
      Term tp = wrap_poly_tp(decode_tp(x->items[4], lv), lv);
      Term raw_body = wrap_poly_tm(decode_tm(x->items[5], lv), lv, true);
      /* Type the body as written before normalizing it: normalization is only
       * known to terminate on a typed term, and it may erase an ill-typed argument. */
      Term raw_tp = 0;
      Occ oraw = (tp && raw_body) ? prove_has_type(0, T_TPLN, raw_body, &raw_tp) : 0;
      Term body = (oraw && raw_tp == tp) ? tm_nf(raw_body) : 0;
      Term inf_tp = 0;
      Occ oty = body ? prove_has_type(0, T_TPLN, body, &inf_tp) : 0;
      if (!tp || !oty || inf_tp != tp) {
        fprintf(stderr, "mg_tcalc: DEF %s type check failed\n", name);
        ok = false; break;
      }
      if (syms[h].has_term && syms[h].tp != tp) {
        fprintf(stderr, "mg_tcalc: restated DEF %s type mismatch\n", name);
        ok = false; break;
      }
      if (syms[h].has_term && !syms[h].is_param) {
        if (syms[h].def && mg_conv(syms[h].def, body)) st->repeated++;
        else {
          fprintf(stderr, "mg_tcalc: restated DEF %s body mismatch\n", name);
          ok = false; break;
        }
      } else {
        Occ keep[1] = { oty };
        Term inst[3] = { syms[h].nterm, body, tp };
        Occ socc = commit_mg_step(R_DECL_DEF, keep, inst);
        if (!socc) { ok = false; break; }
        syms[h].has_term = true;
        syms[h].is_param = false;
        syms[h].tp = tp;
        syms[h].def = body;
        syms[h].sig_occ = socc;
        syms[h].term_seq = next_decl_seq++;
        st->defs++;
        push_dk_item((DkEmitItem){ .kind = DK_ITEM_DEF, .sym = h, .tp = tp, .body = body });
      }
    } else if (sx_is_atom(hd, "AXIOM") && x->len == 6) {
      const char *name = x->items[1]->text;
      uint32_t h = sym_intern_n(x->items[2]->text, x->items[2]->len);
      uint32_t lv = (uint32_t)x->items[3]->val;
      Term prop = wrap_poly_tm(decode_tm(x->items[4], lv), lv, false);
      Occ oprop = prop ? prove_is_prop(0, T_TPLN, prop) : 0;
      if (!oprop) {
        fprintf(stderr, "mg_tcalc: AXIOM %s is not a proposition\n", name);
        ok = false; break;
      }
      if (syms[h].has_known) {
        if (!mg_conv(syms[h].prop, prop)) {
          fprintf(stderr, "mg_tcalc: restated AXIOM %s proposition mismatch\n", name);
          ok = false; break;
        }
        st->repeated++;
      } else {
        if (!g_allow_axioms) {
          fprintf(stderr, "mg_tcalc: AXIOM %s refused by --axioms none policy\n", name);
          ok = false; break;
        }
        Occ keep[1] = { oprop };
        Term inst[2] = { syms[h].nterm, prop };
        Occ ksig = 0;
        Occ kocc = commit_mg_step_extra(R_DECL_AXIOM, keep, inst, &ksig);
        if (!kocc || !ksig) { ok = false; break; }
        syms[h].has_known = true;
        syms[h].prop = prop;
        syms[h].known_occ = kocc;
        syms[h].known_sig_occ = ksig;
        st->axioms++;
        push_dk_item((DkEmitItem){ .kind = DK_ITEM_AXIOM, .sym = h, .tp = tm_nf(prop) });
      }
    } else if ((sx_is_atom(hd, "THM") || sx_is_atom(hd, "CONJ")) && x->len == 7) {
      if (pending) { ok = false; break; }
      pending_name = x->items[1]->text;
      pending_sym  = sym_intern_n(x->items[2]->text, x->items[2]->len);
      pending_levels = (uint32_t)x->items[4]->val;
      pending_prop = wrap_poly_tm(decode_tm(x->items[5], pending_levels), pending_levels, false);
      pending_prop_occ = pending_prop ? prove_is_prop(0, T_TPLN, pending_prop) : 0;
      if (!pending_prop_occ) {
        fprintf(stderr, "mg_tcalc: THM %s is not a proposition\n", pending_name);
        ok = false; break;
      }
      pending = !sx_is_atom(hd, "CONJ");
      pending_proved = false;
    } else if (sx_is_atom(hd, "PROOF") && x->len == 3) {
      if (!pending || pending_proved) {
        fprintf(stderr, "mg_tcalc: PROOF requires one unproved pending theorem\n");
        ok = false; break;
      }
      MgPf *pf = wrap_poly_pf(decode_pf(x->items[2], pending_levels), pending_levels);
      push_dk_item((DkEmitItem){
        .kind = DK_ITEM_THM,
        .sym = pending_sym,
        .thm_seq = ++dk_thm_seq,
        .tp = tm_nf(pending_prop),
        .pf = pf
      });
      Term inferred = 0;
      Occ pocc = check_proof_tree(T_CTX_EMPTY, pf, &inferred);
      if (!pocc || !mg_conv(inferred, pending_prop)) {
        fprintf(stderr, "mg_tcalc: PROOF of %s refused\n", pending_name);
        ok = false; break;
      }
      Term ca[2] = { inferred, pending_prop };
      Occ c_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_CONV, ca));
      Occ keep[3] = { pending_prop_occ, pocc, c_occ };
      Term inst[3] = { syms[pending_sym].nterm, pending_prop, inferred };
      Occ ksig = 0;
      Occ kocc = commit_mg_step_extra(R_THM_IMPORT, keep, inst, &ksig);
      if (!kocc || !ksig) { ok = false; break; }
      if (!syms[pending_sym].has_known) {
        syms[pending_sym].has_known = true;
        syms[pending_sym].prop = pending_prop;
        syms[pending_sym].known_occ = kocc;
        syms[pending_sym].known_sig_occ = ksig;
        free(syms[pending_sym].thm_name);
        syms[pending_sym].thm_name = strdup(pending_name);
      }
      st->thms++;
      pending_proved = true;
      if (!g_emit_dk_path) free_pf_chunks();
    } else if (sx_is_atom(hd, "QED") && x->len == 1) {
      if (!pending || !pending_proved) {
        fprintf(stderr, "mg_tcalc: QED requires a checked proof\n");
        ok = false; break;
      }
      pending = false;
      pending_proved = false;
    } else if (sx_is_atom(hd, "DELTA") || sx_is_atom(hd, "USESKNOWN")) {
      /* informational dependency lines in upstream exports */
    } else {
      fprintf(stderr, "mg_tcalc: unexpected form in %s\n", path);
      ok = false; break;
    }
    free_sx_arena();
  }

  if (g_emit_dk_path) {
    if (!emit_dk_file(g_emit_dk_path, ok && !pending)) ok = false;
  }
  free_pf_chunks();
  free_sx_arena();
  free(buf);
  return ok && !pending;
}

/* ---- Self-test: all 8 rules + negative controls + Subproof Space Reach ---- */
static bool run_self_test(void) {
  init_mg_kernel(PROF_EGAL);

  /* Declare polymorphic parameter P_self : Pi A. A -> prop via R_DECL_PARAM */
  uint32_t sym_P = sym_intern("P_self");
  Term vA = mk_tp_var(0);
  Term body_tp_P = mk_tp_arr(vA, T_TP_PROP);
  Occ owf_P = prove_plain_wf(1, body_tp_P);
  if (!owf_P) return false;
  Term tp_P = mk_tp_all(body_tp_P);
  Occ keep_P[1] = { owf_P };
  Term inst_P[4] = { mk_int(1), body_tp_P, syms[sym_P].nterm, tp_P };
  Occ socc_P = commit_mg_step(R_DECL_PARAM, keep_P, inst_P);
  if (!socc_P) return false;
  syms[sym_P].has_term = true;
  syms[sym_P].is_param = true;
  syms[sym_P].tp = tp_P;
  syms[sym_P].sig_occ = socc_P;
  syms[sym_P].term_seq = next_decl_seq++;

  /* Construct proof of: TAll A. All x:A. Imp(P A x, P A x)
     using typeLam, termLam, proofLam, hyp! */
  Term px = mk_tm_ap(mk_tm_tap(mk_tm_name(sym_P), vA), mk_tm_db(0));
  MgPf *p_hyp = alloc_pf(PF_HYP); p_hyp->n = 0;
  MgPf *p_plam = alloc_pf(PF_PLAM); p_plam->t = px; p_plam->p = p_hyp;
  MgPf *p_tlam = alloc_pf(PF_TLAM); p_tlam->tp = vA; p_tlam->p = p_plam;
  MgPf *p_tplam = alloc_pf(PF_TPLAM); p_tplam->p = p_tlam;

  Term prop_poly = 0;
  Occ occ_poly = check_proof_tree(T_CTX_EMPTY, p_tplam, &prop_poly);
  if (!occ_poly) return false;

  /* Publish as known K_id via R_THM_IMPORT */
  uint32_t sym_K = sym_intern("K_id");
  Occ oprop_poly = prove_is_prop(0, T_TPLN, prop_poly);
  if (!oprop_poly) return false;
  Term ca[2] = { prop_poly, prop_poly };
  Occ c_occ = tc_post(SPACE_HELPER, tc_app(C_HELPER_CONV, ca));
  Occ keep_imp[3] = { oprop_poly, occ_poly, c_occ };
  Term inst_imp[3] = { syms[sym_K].nterm, prop_poly, prop_poly };
  Occ ksig = 0;
  Occ kocc = commit_mg_step_extra(R_THM_IMPORT, keep_imp, inst_imp, &ksig);
  if (!kocc || !ksig) return false;
  syms[sym_K].has_known = true;
  syms[sym_K].prop = prop_poly;
  syms[sym_K].known_occ = kocc;
  syms[sym_K].known_sig_occ = ksig;

  /* Now use known, typeApp (A := set), termApp (x := Empty), proofLam, and proofApp
     to prove Imp(P set Empty, P set Empty) */
  Term p_empty = mk_tm_ap(mk_tm_tap(mk_tm_name(sym_P), T_TP_SET), mk_tm_prim(2));
  MgPf *p_kn = alloc_pf(PF_KNOWN); p_kn->n = sym_K;
  MgPf *p_tpap = alloc_pf(PF_TPAP); p_tpap->p = p_kn; p_tpap->tp = T_TP_SET;
  MgPf *p_tmap = alloc_pf(PF_TMAP); p_tmap->p = p_tpap; p_tmap->t = mk_tm_prim(2);
  MgPf *p_pfap = alloc_pf(PF_PFAP); p_pfap->p = p_tmap; p_pfap->q = p_hyp;
  MgPf *p_full = alloc_pf(PF_PLAM); p_full->t = p_empty; p_full->p = p_pfap;

  Term prop_inst = 0;
  Occ occ_inst = check_proof_tree(T_CTX_EMPTY, p_full, &prop_inst);
  if (!occ_inst || prop_inst != mk_tm_imp(p_empty, p_empty)) return false;

  /* Verify all 8 rules fired at least once */
  for (int r = 1; r <= 8; r++) {
    if (stat_rule_fires[r] == 0) return false;
  }

  /* Negative control 1: Gpa placeholder must be refused */
  MgPf *p_gpa = alloc_pf(PF_GPA);
  Term bad_prop = 0;
  if (check_proof_tree(T_CTX_EMPTY, p_gpa, &bad_prop) != 0) return false;

  /* Negative control 2: ill-typed termApp (applying All x:set to a Prop term) must be refused */
  MgPf *p_bad_tmap = alloc_pf(PF_TMAP);
  p_bad_tmap->p = p_tpap;
  p_bad_tmap->t = p_empty; /* has type Prop, not set */
  if (check_proof_tree(T_CTX_EMPTY, p_bad_tmap, &bad_prop) != 0) return false;

  /* Negative control 3: typeLam in non-empty context must be refused */
  Term non_empty_ctx = mk_ctx(0, T_TPLN, mk_tmlc(p_empty, T_TMLN));
  if (check_proof_tree(non_empty_ctx, p_tplam, &bad_prop) != 0) return false;

  /* Subproof Space Birth + Reach (Rows 3-5: NamedSpaces, SpacesCreation, NamedSpacesReach):
     Birth a fresh subproof space s1 for hypothesis p_empty in non_empty_ctx. */
  Term s1 = tc_name(tc_space_sort(), tc_fresh_name());
  Term auth_args[2] = { non_empty_ctx, p_empty };
  Occ auth_occ = tc_post(SPACE_HELPER, tc_app(C_SUB_AUTH, auth_args));
  Occ keep_b[1] = { auth_occ };
  Term inst_b[3] = { s1, non_empty_ctx, p_empty };
  Occ h1_occ = tc_fire(R_SUB_BIRTH, NULL, keep_b, inst_b);
  if (!h1_occ || !tc_space_born(s1)) return false;
  Occ sub_hyp_occ = tc_last_extra(1);
  if (!sub_hyp_occ || tc_occ_space(sub_hyp_occ) != s1) return false;

  /* Negative control 4 (Births.fresh): birthing s1 a second time must be refused */
  if (tc_fire(R_SUB_BIRTH, NULL, keep_b, inst_b) != 0) return false;

  /* Negative control 5 (NamedSpacesReach): sibling subproof with only handle(s2)
     cannot discharge sub_hyp_occ in s1 */
  Term s2 = tc_name(tc_space_sort(), tc_fresh_name());
  Term s2a[1] = { s2 };
  Term seeds_wrong[2] = { tc_space_term(SPACE_THM), tc_app(C_HANDLE, s2a) };
  Occ keep_u[1] = { sub_hyp_occ };
  if (tc_fire_reach(R_SUB_USE_HYP, NULL, keep_u, inst_b, seeds_wrong, 2) != 0)
    return false;

  /* Positive control (NamedSpacesReach): holder of handle(s1) CAN discharge sub_hyp_occ */
  Term seeds_right[2] = { tc_space_term(SPACE_THM), tc_term(h1_occ) };
  Occ sub_thm = tc_fire_reach(R_SUB_USE_HYP, NULL, keep_u, inst_b, seeds_right, 2);
  if (!sub_thm) return false;

  free_pf_chunks();
  return true;
}

static uint32_t find_known_by_thm_name(const char *name) {
  for (uint32_t i = 1; i <= nsyms; i++) {
    if (syms[i].has_known && syms[i].thm_name && strcmp(syms[i].thm_name, name) == 0)
      return i;
  }
  return 0;
}

/* Track 4 Runtime Gate: verifies that R_ACT_GATE fires ONLY when the requested
   action has a genuine proof in SPACE_THM and the target space is within capability reach.
   Tests 1 positive + all 4 required refusals (harm to another, harm to self, outside reach,
   proof for a different action) against the live SPACE_THM of bodhisattva_tower.sexpr. */
static bool run_bodhisattva_gate(void) {
  uint32_t id_safe   = find_known_by_thm_name("model_safe_step_holds");
  uint32_t id_idem   = find_known_by_thm_name("model_safe_step_idempotent");
  uint32_t id_hother = find_known_by_thm_name("countermodel_harm_other_refused");
  uint32_t id_hself  = find_known_by_thm_name("countermodel_harm_self_refused");
  if (!id_safe || !id_idem || !id_hother || !id_hself) return false;

  Term prop_safe = syms[id_safe].prop;
  Occ  occ_safe  = syms[id_safe].known_occ;
  Term prop_idem = syms[id_idem].prop;

  /* Extract the inner negated propositions from ~ BodhisattvaSafeStep ... and ~ PreservesAgency ... */
  uint8_t k; uint32_t h; int ar; const Term *a;
  tc_node(syms[id_hother].prop, &k, &h, &ar, &a);
  if (ar < 1) return false;
  Term prop_harm_other = a[0];

  tc_node(syms[id_hself].prop, &k, &h, &ar, &a);
  if (ar < 1) return false;
  Term prop_harm_self = a[0];

  /* Birth two actuator spaces via R_SUB_BIRTH: s_reach (in capability reach) and s_outside (outside reach) */
  Term s_reach   = tc_name(tc_space_sort(), tc_fresh_name());
  Term s_outside = tc_name(tc_space_sort(), tc_fresh_name());
  Term auth_a[2] = { T_CTX_EMPTY, prop_safe };
  Occ auth_occ = tc_post(SPACE_HELPER, tc_app(C_SUB_AUTH, auth_a));
  Occ keep_b[1] = { auth_occ };
  Term inst_b1[3] = { s_reach, T_CTX_EMPTY, prop_safe };
  Term inst_b2[3] = { s_outside, T_CTX_EMPTY, prop_safe };
  Occ h_reach   = tc_fire(R_SUB_BIRTH, NULL, keep_b, inst_b1);
  Occ h_outside = tc_fire(R_SUB_BIRTH, NULL, keep_b, inst_b2);
  if (!h_reach || !h_outside || !tc_space_born(s_reach) || !tc_space_born(s_outside))
    return false;

  /* Agent's capability seeds include SPACE_THM and handle(s_reach), NOT handle(s_outside) */
  Term seeds_agent[2] = { tc_space_term(SPACE_THM), tc_term(h_reach) };

  /* Refusal 1: Harm to another (prop_harm_other has no proof in SPACE_THM; countermodel proved its negation) */
  Term req_ho_a[1] = { prop_harm_other };
  Occ req_ho = tc_post_at(s_reach, tc_app(C_ACT_REQ, req_ho_a), false);
  Occ take_ho[1] = { req_ho };
  Occ keep_ho1[1] = { syms[id_hother].known_occ };
  Occ keep_ho2[1] = { occ_safe };
  Term inst_ho[2] = { s_reach, prop_harm_other };
  if (tc_fire_reach(R_ACT_GATE, take_ho, keep_ho1, inst_ho, seeds_agent, 2) != 0) return false;
  if (tc_fire_reach(R_ACT_GATE, take_ho, keep_ho2, inst_ho, seeds_agent, 2) != 0) return false;
  if (!tc_alive(req_ho)) return false;

  /* Refusal 2: Harm to self (prop_harm_self has no proof in SPACE_THM; countermodel proved its negation) */
  Term req_hs_a[1] = { prop_harm_self };
  Occ req_hs = tc_post_at(s_reach, tc_app(C_ACT_REQ, req_hs_a), false);
  Occ take_hs[1] = { req_hs };
  Occ keep_hs1[1] = { syms[id_hself].known_occ };
  Occ keep_hs2[1] = { occ_safe };
  Term inst_hs[2] = { s_reach, prop_harm_self };
  if (tc_fire_reach(R_ACT_GATE, take_hs, keep_hs1, inst_hs, seeds_agent, 2) != 0) return false;
  if (tc_fire_reach(R_ACT_GATE, take_hs, keep_hs2, inst_hs, seeds_agent, 2) != 0) return false;
  if (!tc_alive(req_hs)) return false;

  /* Refusal 3: Outside capability reach (valid proof occ_safe, but target space s_outside is unreached) */
  Term req_out_a[1] = { prop_safe };
  Occ req_out = tc_post_at(s_outside, tc_app(C_ACT_REQ, req_out_a), false);
  Occ take_out[1] = { req_out };
  Occ keep_out[1] = { occ_safe };
  Term inst_out[2] = { s_outside, prop_safe };
  if (tc_fire_reach(R_ACT_GATE, take_out, keep_out, inst_out, seeds_agent, 2) != 0) return false;
  if (!tc_alive(req_out)) return false;

  /* Refusal 4: Proof is for a different action (requesting prop_idem with proof occ_safe of prop_safe) */
  Term req_diff_a[1] = { prop_idem };
  Occ req_diff = tc_post_at(s_reach, tc_app(C_ACT_REQ, req_diff_a), false);
  Occ take_diff[1] = { req_diff };
  Occ keep_diff[1] = { occ_safe };
  Term inst_diff1[2] = { s_reach, prop_idem };
  Term inst_diff2[2] = { s_reach, prop_safe };
  if (tc_fire_reach(R_ACT_GATE, take_diff, keep_diff, inst_diff1, seeds_agent, 2) != 0) return false;
  if (tc_fire_reach(R_ACT_GATE, take_diff, keep_diff, inst_diff2, seeds_agent, 2) != 0) return false;
  if (!tc_alive(req_diff)) return false;

  /* Positive Control: Safe action prop_safe in s_reach with matching proof occ_safe inside capability reach */
  Term req_ok_a[1] = { prop_safe };
  Occ req_ok = tc_post_at(s_reach, tc_app(C_ACT_REQ, req_ok_a), false);
  Occ take_ok[1] = { req_ok };
  Occ keep_ok[1] = { occ_safe };
  Term inst_ok[2] = { s_reach, prop_safe };
  Occ commit_occ = tc_fire_reach(R_ACT_GATE, take_ok, keep_ok, inst_ok, seeds_agent, 2);
  if (!commit_occ || tc_occ_space(commit_occ) != s_reach || tc_alive(req_ok)) return false;

  return true;
}

int main(int argc, char **argv) {
  tc_stack_guard(argv);
  int profile = PROF_EGAL;
  bool did_self_test = false;
  bool chain_mode = false;
  bool inited = false;
  int files_run = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--self-test") == 0) {
      double t0 = now_ms();
      if (!run_self_test()) {
        fprintf(stderr, "mg_tcalc: self-test FAILED\n");
        return 1;
      }
      printf("mg_tcalc self-test: 8 rules + 5 negative controls + subproof-reach passed (%.2f ms)\n",
             now_ms() - t0);
      did_self_test = true;
      inited = false;
    } else if (strcmp(argv[i], "--chain") == 0) {
      chain_mode = true;
      inited = false;
    } else if (strcmp(argv[i], "--no-axioms") == 0) {
      g_allow_axioms = false;
    } else if (strcmp(argv[i], "--axioms") == 0 && i + 1 < argc) {
      i++;
      if (strcmp(argv[i], "all") == 0) g_allow_axioms = true;
      else if (strcmp(argv[i], "none") == 0) g_allow_axioms = false;
      else {
        fprintf(stderr, "mg_tcalc: unknown --axioms policy '%s' (expected all or none)\n", argv[i]);
        return 1;
      }
    } else if (strcmp(argv[i], "--emit-dk") == 0 && i + 1 < argc) {
      g_emit_dk_path = argv[++i];
    } else if (strcmp(argv[i], "--bodhisattva-gate") == 0) {
      double t0 = now_ms();
      if (!inited || !run_bodhisattva_gate()) {
        fprintf(stderr, "mg_tcalc: --bodhisattva-gate FAILED\n");
        return 1;
      }
      printf("mg_tcalc bodhisattva-gate: 1/1 safe action admitted + 4/4 refusals (harm_other, harm_self, outside_reach, wrong_action_proof) verified (%.2f ms)\n",
             now_ms() - t0);
    } else if (strcmp(argv[i], "--profile") == 0 && i + 1 < argc) {
      i++;
      if (strcmp(argv[i], "egal") == 0) profile = PROF_EGAL;
      else if (strcmp(argv[i], "hf") == 0) profile = PROF_HF;
      else if (strcmp(argv[i], "mizar") == 0) profile = PROF_MIZAR;
      else if (strcmp(argv[i], "hoas") == 0) profile = PROF_HOAS;
      else {
        fprintf(stderr, "mg_tcalc: unknown profile '%s' (expected egal, hf, mizar, or hoas)\n", argv[i]);
        return 1;
      }
      inited = false;
    } else {
      double t0 = now_ms();
      if (!chain_mode || !inited) {
        init_mg_kernel(profile);
        inited = true;
      }
      uint64_t fires_before = 0;
      for (int r = 1; r <= 8; r++) fires_before += stat_rule_fires[r];
      uint64_t tc_fires_before = stat_total_tc_fires;
      ReplayStats st = {0};
      bool ok = replay_sexpr_file(argv[i], &st);
      g_emit_dk_path = NULL;
      if (!ok) {
        fprintf(stderr, "mg_tcalc: FAILED on %s\n", argv[i]);
        return 1;
      }
      uint64_t fires_after = 0;
      for (int r = 1; r <= 8; r++) fires_after += stat_rule_fires[r];
      uint64_t tc_fires_after = stat_total_tc_fires;
      printf("mg_tcalc [%s%s] %s: %u prims, %u params, %u defs, %u axioms, %u thms, %" PRIu64 " proof fires (%" PRIu64 " total tc fires) in %.2f ms\n",
             profile_label(profile),
             chain_mode ? ":chain" : "", argv[i],
             st.prims, st.params, st.defs, st.axioms, st.thms,
             fires_after - fires_before, tc_fires_after - tc_fires_before, now_ms() - t0);
      files_run++;
    }
  }

  if (!did_self_test && files_run == 0) {
    if (!run_self_test()) return 1;
    printf("mg_tcalc self-test: passed\n");
  }
  return 0;
}
