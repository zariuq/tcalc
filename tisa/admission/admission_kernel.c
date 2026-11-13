/* admission_kernel.c: the kernel side of sealed guards over spaces and protected value facts.
   Each check prints "holds" or "VIOLATED"; the exit status is 1 if any is violated, 2 if a scene
   could not be set up. Every firing below runs after tc_seal, from an untrusted caller.

   Theory: W a word sort; F a provable sort; Val(w), Req(w, w), Out(w, w, w), Pair(w, w) : F.
   Spaces: 1 an evidence space (producers fixed by tc_publishers), 2 protected, 3 open.
   Sealed functions: add (op, 2 -> 1), dbl (op, 1 -> 1), refuse13 (op: no value at 13), lt100 (guard). */
#include "../../tcalc.h"
#include "../tc_theory_inspect.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int violations, setups;
#define HOLDS(c, what) do { if (c) printf("  holds     %s\n", what); else { printf("  VIOLATED  %s\n", what); violations++; } } while (0)
#define SETUP(c) do { if (!(c)) { printf("  NO SCENE  line %d: %s\n", __LINE__, #c); setups++; return; } } while (0)

static unsigned long add_calls;
static bool fn_add(const uint64_t *in, uint64_t *out) { add_calls++; out[0] = in[0] + in[1]; return true; }
static bool fn_dbl(const uint64_t *in, uint64_t *out) { out[0] = 2u * in[0]; return true; }
static bool fn_refuse13(const uint64_t *in, uint64_t *out) { if (in[0] == 13u) return false; out[0] = in[0]; return true; }
static bool fn_const7(const uint64_t *in, uint64_t *out) { (void)in; out[0] = 7u; return true; }
static bool g_lt100(const uint64_t *in, uint64_t *out) { (void)out; return in[0] < 100u; }
static const uint8_t H0[32] = { 1 }, H1[32] = { 2 }, H2[32] = { 3 }, H3[32] = { 4 }, H4[32] = { 5 };

static int W, F, Val, Req, Out, Pair, Sref;
static int f_add, f_dbl, f_ref, f_lt, f_c7;
static Term w(uint64_t v) { return tc_name((uint16_t)W, v); }
static Term val(Term x) { return tc_app(Val, &x); }
static Term req(Term x, Term y) { Term a[2] = { x, y }; return tc_app(Req, a); }
static Term out3(Term x, Term y, Term s) { Term a[3] = { x, y, s }; return tc_app(Out, a); }
static Term pair(Term x, Term y) { Term a[2] = { x, y }; return tc_app(Pair, a); }

static void theory(void) {
    if (!tc_init(1u << 14, 1u << 10)) { printf("NO SCENE: tc_init\n"); exit(2); }
    W = tc_sort(SORT_WORD); F = tc_sort(SORT_PROVABLE);
    Binder b[3] = { { (uint16_t)W, 0, 0 }, { (uint16_t)W, 0, 0 }, { (uint16_t)W, 0, 0 } };
    Val = tc_con((uint16_t)F, 0, 1, b); Req = tc_con((uint16_t)F, 0, 2, b);
    Out = tc_con((uint16_t)F, 0, 3, b); Pair = tc_con((uint16_t)F, 0, 2, b);
    Binder sb = { tc_space_sort(), 0, 0 };
    Sref = tc_con((uint16_t)F, 0, 1, &sb);                /* Sref(s): a fact naming a space */
    f_add = tc_fn("test.add", TC_FN_OP, 2, 1, fn_add, H0);
    f_dbl = tc_fn("test.dbl", TC_FN_OP, 1, 1, fn_dbl, H1);
    f_ref = tc_fn("test.refuse13", TC_FN_OP, 1, 1, fn_refuse13, H2);
    f_lt  = tc_fn("test.lt100", TC_FN_GUARD, 1, 0, g_lt100, H3);
    f_c7  = tc_fn("test.const7", TC_FN_OP, 0, 1, fn_const7, H4);
    if (W <= 0 || F <= 0 || Val < 0 || Req < 0 || Out < 0 || Pair < 0 || f_add < 0 || f_dbl < 0 || f_ref < 0 || f_lt < 0 || f_c7 < 0) {
        printf("NO SCENE: theory\n"); exit(2);
    }
}
static bool ctx(int n) {
    Binder b[16];
    for (int i = 0; i < n; i++) b[i] = (Binder){ (uint16_t)W, 0, 0 };
    return tc_ctx(n, b);
}
/* The producer: TAKE Req(x, y) @3 (or KEEP it); KEEP Val(z) @2; OP a := add(x, z); OP r := refuse13(a);
   OP s := dbl(r); GUARD lt100(s); MAKE Out(x, y, s) @1.  Holes: x0 y1 z2 a3 r4 s5. */
static Rule producer_k(bool take) {
    Rule r;
    memset(&r, 0, sizeof r);
    r.fresh = -1;
    if (take) { r.ntake = 1; r.take[0] = (Pat){ req(tc_v(0), tc_v(1)), 3 }; }
    else { r.nkeep = 1; r.keep[0] = (Pat){ req(tc_v(0), tc_v(1)), 3 }; }
    r.keep[r.nkeep++] = (Pat){ val(tc_v(2)), 2 };
    r.nop = 3;
    r.op[0] = (TcOpUse){ .fn = (int16_t)f_add, .in = { 0, 2 }, .out = { 3 } };
    r.op[1] = (TcOpUse){ .fn = (int16_t)f_ref, .in = { 3 }, .out = { 4 } };
    r.op[2] = (TcOpUse){ .fn = (int16_t)f_dbl, .in = { 4 }, .out = { 5 } };
    r.nguard = 1; r.guard[0] = (TcGuardUse){ .fn = (int16_t)f_lt, .in = { 5 } };
    r.make = (Pat){ out3(tc_v(0), tc_v(1), tc_v(5)), 1 };
    return r;
}
static Rule producer(void) { return producer_k(true); }

/* The board: every occurrence id up to hi, alive or not, with its term; and the name counter. */
typedef struct { Occ hi; bool alive[512]; Term term[512]; uint64_t names; } Snap;
static void snap(Snap *s, Occ hi) {
    s->hi = hi < 511 ? hi : 511; s->names = tc_next_name();
    for (Occ o = 1; o <= s->hi; o++) { s->alive[o] = tc_alive(o); s->term[o] = s->alive[o] ? tc_term(o) : 0; }
}
static bool same(const Snap *a, Occ hi) {
    Snap b; snap(&b, hi);
    if (a->names != b.names) return false;
    for (Occ o = 1; o <= a->hi; o++) if (a->alive[o] != b.alive[o] || a->term[o] != b.term[o]) return false;
    for (Occ o = a->hi + 1; o <= b.hi; o++) if (b.alive[o]) return false;
    return true;
}

/* Routes that commit a firing; each returns the made occurrence or 0. */
typedef struct { const Occ *take, *keep; const Term *inst; int rule; } Fire;
static Occ r_fire(Fire f) { return tc_fire(f.rule, f.take, f.keep, f.inst); }
static Occ r_reach(Fire f) { Term s[3] = { tc_space_term(1), tc_space_term(2), tc_space_term(3) }; return tc_fire_reach(f.rule, f.take, f.keep, f.inst, s, 3); }
static Occ r_flat(Fire f) { return tc_flat_fire(f.rule, f.keep, f.inst, 0); }
static Occ r_prepared(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    Occ o = 0;
    return tc_eval_prepared_ex(&st, false, false, false, false, true, NULL, NULL, NULL, NULL, &o) == TC_PREP_OK ? o : 0;
}
static Occ r_prepared_dest(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst, .dest = 1 };
    Occ o = 0;
    return tc_eval_prepared_ex(&st, true, true, true, false, true, NULL, NULL, NULL, NULL, &o) == TC_PREP_OK ? o : 0;
}
static Occ r_commit(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    TcAdmissionReceipt rc;
    return tc_commit_prepared(&st, &rc) ? rc.out : 0;
}
static TcPreparedStep cursor_step;
static int cursor_left;
static bool cursor_next(void *c, TcPreparedStep *o) { (void)c; if (!cursor_left) return false; cursor_left--; *o = cursor_step; return true; }
static Occ r_cursor(Fire f) {
    cursor_step = (TcPreparedStep){ .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    cursor_left = 1;
    TcCandidateCursor cur = { NULL, cursor_next };
    TcAdmissionReceipt rc;
    return tc_step_cursor(&cur, &rc) == 1 ? rc.out : 0;
}
/* The evaluation-only variant answers without committing: 0 admitted, otherwise its code. */
static int r_eval_only(Fire f) {
    TcPreparedStep st = { .rule = f.rule, .take = f.take, .keep = f.keep, .inst = f.inst };
    return tc_eval_prepared_ex(&st, false, false, false, false, false, NULL, NULL, NULL, NULL, NULL);
}
typedef Occ (*Route)(Fire);
static const struct { const char *name; Route r; } ROUTES[] = {
    { "tc_fire", r_fire }, { "tc_fire_reach", r_reach }, { "tc_flat_fire", r_flat },
    { "tc_eval_prepared_ex commit", r_prepared }, { "tc_eval_prepared_ex commit with dest", r_prepared_dest },
    { "tc_commit_prepared", r_commit }, { "tc_step_cursor", r_cursor },
};
#define NROUTES (int)(sizeof ROUTES / sizeof ROUTES[0])

static void registry_controls(void) {
    printf("registry\n");
    theory();
    char name[] = "test.mutable";
    int id = tc_fn(name, TC_FN_OP, 1, 1, fn_dbl, H0);
    name[0] = 'X';
    TcFnInfo fi;
    HOLDS(id >= 0 && tc_fn_info(id, &fi) && !strcmp(fi.name, "test.mutable") && fi.fn == fn_dbl && fi.contract_sha256[0] == 1,
          "an entry keeps its own copy of the name and hash (a caller's later change of its buffer changes nothing)");
    HOLDS(tc_fn("g", TC_FN_GUARD, 1, 1, g_lt100, H0) < 0, "a guard with an output is refused");
    HOLDS(tc_fn("o", TC_FN_OP, 1, 0, fn_dbl, H0) < 0 && tc_fn("o", TC_FN_OP, 1, 5, fn_dbl, H0) < 0, "an operation with 0 or more than 4 outputs is refused");
    HOLDS(tc_fn("o", TC_FN_OP, 17, 1, fn_dbl, H0) < 0, "more than 16 inputs is refused");
    HOLDS(tc_fn("o", 3, 1, 1, fn_dbl, H0) < 0, "an unknown kind is refused");
    HOLDS(tc_fn(NULL, TC_FN_OP, 1, 1, fn_dbl, H0) < 0 && tc_fn("o", TC_FN_OP, 1, 1, NULL, H0) < 0 && tc_fn("o", TC_FN_OP, 1, 1, fn_dbl, NULL) < 0,
          "a missing name, function or contract hash is refused");
    char longname[200]; memset(longname, 'a', sizeof longname - 1); longname[sizeof longname - 1] = 0;
    HOLDS(tc_fn(longname, TC_FN_OP, 1, 1, fn_dbl, H0) < 0, "a name longer than the registry keeps is refused");
    tc_seal();
    HOLDS(tc_fn("late", TC_FN_OP, 1, 1, fn_dbl, H0) < 0, "the seal closes the registry");
    HOLDS(tc_fn_count() == 6, "the registry holds exactly the entries made before the seal");
}

static void word_sort_controls(void) {
    printf("word sorts\n");
    theory();
    HOLDS(tc_con((uint16_t)W, 0, 0, NULL) < 0, "no constructor returns a word sort");
    HOLDS(tc_bv((uint16_t)W, 0) == 0, "a word sort has no bound variable");
    Binder bw = { (uint16_t)W, 1, 0 };
    HOLDS(!tc_ctx(1, &bw), "no binder has a word sort");
    ctx(1);
    HOLDS(tc_def((uint16_t)W, 0, 1, 0, tc_v(0)) < 0, "no definition returns a word sort");
    Rule fr; memset(&fr, 0, sizeof fr);
    fr.fresh = 0; fr.make = (Pat){ val(tc_v(0)), 3 };
    HOLDS(tc_rule(&fr) < 0, "a fresh hole has no word sort");
    tc_seal();
    HOLDS(tc_post(3, val(w(UINT64_MAX))) != 0 && tc_post(3, val(w(5))) != 0, "a word is a literal: it needs no minting");
}

static void rule_shape_controls(void) {
    printf("rule shapes\n");
    theory();
    tc_protect(1); tc_protect(2);
    ctx(6);
    Rule p = producer();
    int rid = tc_rule(&p);
    HOLDS(rid >= 0, "the producer (operations chained in order, a guard on an output) is installed");
    HOLDS((tc_rule_fibre(rid) & FIBRE_FN) && !(tc_rule_fibre(rid) & FIBRE_PURE), "a rule calling functions carries FIBRE_FN and is not pure");
    int fns[8], nf = tc_rule_fns(rid, fns, 8);
    HOLDS(nf == 4 && fns[0] == f_add && fns[1] == f_ref && fns[2] == f_dbl && fns[3] == f_lt, "tc_rule_fns lists the operations in order, then the guards");
    Rule q;
    q = p; q.op[0].in[0] = 5;                              /* reads s, made by a later operation */
    HOLDS(tc_rule(&q) < 0, "an operation reading a later operation's output is refused");
    q = p; q.op[0].in[1] = 3;                              /* reads its own output */
    HOLDS(tc_rule(&q) < 0, "an operation reading its own output is refused");
    q = p; q.op[2].out[0] = 2;                             /* writes z, bound by a keep */
    HOLDS(tc_rule(&q) < 0, "an output bound by a premise is refused");
    q = p; q.op[2].out[0] = 3;                             /* a is computed twice */
    HOLDS(tc_rule(&q) < 0, "an output computed twice is refused");
    q = p; q.nabsent = 1; q.absent[0] = (Pat){ val(tc_v(5)), 1 };
    HOLDS(tc_rule(&q) < 0, "an output in an absent query is refused");
    q = p; q.make = (Pat){ out3(tc_v(0), tc_v(1), tc_v(5)), 1 }; q.inputs = 1ull << 5;
    HOLDS(tc_rule(&q) < 0, "an output declared as an input is refused");
    q = p; q.op[0].fn = (int16_t)f_lt;
    HOLDS(tc_rule(&q) < 0, "a guard used as an operation is refused");
    q = p; q.guard[0].fn = (int16_t)f_add;
    HOLDS(tc_rule(&q) < 0, "an operation used as a guard is refused");
    q = p; q.op[0].fn = 99;
    HOLDS(tc_rule(&q) < 0, "an unregistered function is refused");
    /* inputs must be matched: a hole the caller supplies (an input) cannot feed a function */
    ctx(4);
    Rule u; memset(&u, 0, sizeof u);
    u.fresh = -1; u.inputs = 1; u.nop = 1;
    u.op[0] = (TcOpUse){ .fn = (int16_t)f_dbl, .in = { 0 }, .out = { 1 } };
    u.make = (Pat){ pair(tc_v(0), tc_v(1)), 3 };
    HOLDS(tc_rule(&u) < 0, "an operation reading a caller input (not a matched word) is refused");
    u.nop = 0; u.nguard = 1; u.guard[0] = (TcGuardUse){ .fn = (int16_t)f_lt, .in = { 0 } }; u.make = (Pat){ val(tc_v(0)), 3 };
    HOLDS(tc_rule(&u) < 0, "a guard reading a caller input is refused");
    /* a function's holes are words */
    Binder mixed[3] = { { (uint16_t)W, 0, 0 }, { (uint16_t)F, 0, 0 }, { (uint16_t)W, 0, 0 } };
    tc_ctx(3, mixed);
    Rule m; memset(&m, 0, sizeof m);
    m.fresh = -1; m.nkeep = 1; m.keep[0] = (Pat){ val(tc_v(0)), 2 };
    m.nop = 1; m.op[0] = (TcOpUse){ .fn = (int16_t)f_dbl, .in = { 0 }, .out = { 1 } };
    m.make = (Pat){ val(tc_v(0)), 2 };
    HOLDS(tc_rule(&m) < 0, "an output hole of a non-word sort is refused");
    /* the make-only route computes nothing: a function rule never takes it */
    ctx(1);
    Rule c7; memset(&c7, 0, sizeof c7);
    c7.fresh = -1; c7.nop = 1; c7.op[0] = (TcOpUse){ .fn = (int16_t)f_c7, .out = { 0 } };
    c7.make = (Pat){ val(tc_v(0)), 3 };
    int rc7 = tc_rule(&c7);
    tc_seal();
    Term in99[1] = { w(99) };
    HOLDS(rc7 >= 0 && tc_flat_fire(rc7, NULL, in99, 0) == 0, "tc_flat_fire's make-only path refuses a caller value for a computed hole");
    Occ o7 = rc7 >= 0 ? tc_fire(rc7, NULL, NULL, NULL) : 0;
    HOLDS(o7 && tc_term(o7) == val(w(7)), "and the firing computes it");
}

/* Range restriction: tc_rule, the seal, tc_protect after it, computed spaces, derived rules. */
static void range_controls(void) {
    printf("range restriction\n");
    theory();
    tc_protect(2);
    ctx(2);
    Rule open_make; memset(&open_make, 0, sizeof open_make);
    open_make.fresh = -1; open_make.nkeep = 1; open_make.keep[0] = (Pat){ val(tc_v(0)), 3 };
    open_make.make = (Pat){ pair(tc_v(0), tc_v(1)), 2 };   /* y is made but bound by nothing */
    HOLDS(tc_rule(&open_make) < 0, "a rule making an unbound hole into a protected space is refused by tc_rule");
    open_make.inputs = 1ull << 1;
    int declared = tc_rule(&open_make);
    HOLDS(declared >= 0, "the same rule declaring the hole as an input is installed");
    open_make.inputs = 0; open_make.make.space = 3;
    int late = tc_rule(&open_make);                        /* into 3, protected only after the seal */
    open_make.make.space = 4;
    int bar = tc_rule(&open_make);                         /* into 4, protected before the seal */
    tc_protect(4);
    /* computed spaces: TAKE Sref(s) @3; MAKE at s the fact Val(y), s bound by the take, y by nothing */
    Binder sp[2] = { { tc_space_sort(), 0, 0 }, { (uint16_t)W, 0, 0 } };
    tc_ctx(2, sp);
    Rule dyn; memset(&dyn, 0, sizeof dyn);
    dyn.fresh = -1; dyn.ntake = 1; dyn.take[0] = (Pat){ tc_app(Sref, (Term[1]){ tc_v(0) }), 3 };
    dyn.make = (Pat){ tc_at_space(tc_v(0), val(tc_v(1))), 0 };
    int rdyn = tc_rule(&dyn);                              /* y unbound: allowed only where the space is not protected */
    Term dspace = tc_name(tc_space_sort(), tc_fresh_name());
    Occ ds2 = tc_post(3, tc_app(Sref, (Term[1]){ tc_space_term(2) })), dsd = tc_post(3, tc_app(Sref, (Term[1]){ dspace }));
    Occ s3 = tc_post(3, val(w(1)));
    tc_seal();
    Occ k3[1] = { s3 };
    Term in2[2] = { 0, w(5) };
    HOLDS(late >= 0 && !tc_rule_barred(late) && tc_fire(late, NULL, k3, in2) != 0, "before its space is protected the rule fires");
    HOLDS(bar >= 0 && tc_rule_barred(bar), "the seal bars a rule making an unbound hole into a space protected before it");
    HOLDS(bar >= 0 && tc_fire(bar, NULL, k3, in2) == 0, "a barred rule does not fire");
    HOLDS(declared >= 0 && tc_fire(declared, NULL, k3, in2) != 0, "a declared input is supplied by the caller");
    tc_protect(3);
    HOLDS(tc_rule_barred(late) && tc_fire(late, NULL, k3, in2) == 0, "tc_protect after the seal bars the rule too");
    Term y9[2] = { 0, w(9) };
    Occ t2[1] = { ds2 }, td[1] = { dsd };
    HOLDS(rdyn >= 0 && !tc_rule_barred(rdyn) && tc_fire(rdyn, t2, NULL, y9) == 0 && tc_alive(ds2),
          "a computed space that is protected refuses an unbound made hole (the take stays)");
    Occ od = rdyn >= 0 ? tc_fire(rdyn, td, NULL, y9) : 0;
    HOLDS(od && tc_occ_space(od) == dspace, "the same rule makes into a dynamic space");
}

static void derived_controls(void) {
    printf("derived rules\n");
    theory();
    tc_protect(2);
    ctx(1);
    Rule ax; memset(&ax, 0, sizeof ax);
    ax.fresh = -1; ax.inputs = 1; ax.make = (Pat){ val(tc_v(0)), 2 };   /* |- Val(x), x from the caller */
    int rax = tc_rule(&ax);
    tc_seal();
    ctx(1);
    Step st = { .kind = ST_RULE, .rule = rax, .inst = (Term[1]){ tc_v(0) } };
    int lid = tc_promote(1, 2, 0, NULL, val(tc_v(0)), &st, 1);
    TcInspectRule ir;
    HOLDS(lid >= 0 && tc_inspect_rule(lid, &ir, NULL) && ir.decl_rule.inputs == 1 && !tc_rule_barred(lid),
          "a derived rule's conclusion hole its hypotheses do not bind is its declared input");
    Term in5[1] = { w(5) };
    HOLDS(lid >= 0 && tc_fire(lid, NULL, NULL, in5) != 0, "and it fires");
}

/* Evidence spaces: producers fixed before the seal; posts, conversions and other rules refused. */
static void evidence_controls(void) {
    printf("evidence spaces\n");
    theory();
    tc_protect(1); tc_protect(2);
    int Ps = tc_sort(SORT_PROVABLE);                      /* for the active and rho steps */
    Binder pb[2] = { { (uint16_t)Ps, 0, 0 }, { (uint16_t)Ps, 0, 0 } };
    int Q = tc_con((uint16_t)Ps, 0, 1, pb), A = tc_con((uint16_t)Ps, 0, 1, pb), L = tc_con((uint16_t)Ps, 0, 2, pb),
        Ap = tc_con((uint16_t)Ps, 0, 2, pb), K0 = tc_con((uint16_t)Ps, 0, 0, NULL);
    int Ns = tc_sort(SORT_PROVABLE);
    Binder nb = { (uint16_t)Ns, 0, 0 }, prb = { (uint16_t)Ps, 0, 0 };
    int RQ = tc_con((uint16_t)Ns, 0, 1, &prb), RD = tc_con((uint16_t)Ps, 0, 1, &nb);
    tc_set_quote_con(Q, A, L, Ap);
    tc_set_rho_con(RQ, RD, true);
    ctx(6);
    Rule p = producer(), pk = producer_k(false);
    int prod = tc_rule(&p), prodk = tc_rule(&pk);
    Rule other = producer_k(false); other.nguard = 0;     /* a second rule making Out into space 1 */
    int rogue = tc_rule(&other);
    ctx(1);
    Rule withinput; memset(&withinput, 0, sizeof withinput);
    withinput.fresh = -1; withinput.inputs = 1; withinput.make = (Pat){ val(tc_v(0)), 1 };
    int rin = tc_rule(&withinput);
    Rule copy; memset(&copy, 0, sizeof copy);              /* KEEP Val(x) @2 |- Val(x) @2: no producer of 1 */
    copy.fresh = -1; copy.nkeep = 1; copy.keep[0] = (Pat){ val(tc_v(0)), 2 }; copy.make = (Pat){ val(tc_v(0)), 2 };
    int rcopy = tc_rule(&copy);
    SETUP(prod >= 0 && prodk >= 0 && rogue >= 0 && rin >= 0 && rcopy >= 0);
    HOLDS(!tc_publishers(3, &prod, 1), "an unprotected space cannot be an evidence space");
    HOLDS(!tc_publishers(1, &rin, 1), "a producer with an input hole is refused");
    HOLDS(!tc_publishers(1, &rcopy, 1), "a producer that does not make into the space is refused");
    int both[2] = { prod, prodk };
    HOLDS(tc_publishers(1, both, 2), "the producers are declared");
    ctx(1);
    tc_lemma(1, 1); tc_lemma_hyp(val(tc_v(0)));
    HOLDS(tc_lemma_end(-1) < 0, "a derived rule into an evidence space is refused before the seal");
    /* conversion: D(x) := Val(x) */
    ctx(1);
    int D = tc_def((uint16_t)F, 0, 1, 0, val(tc_v(0)));
    Occ v2 = tc_post(2, val(w(3))), v1 = tc_post(1, val(w(3)));
    Occ a1 = tc_post(1, tc_app(A, (Term[1]){ tc_app(Q, (Term[1]){ tc_app(K0, NULL) }) }));
    Occ a2 = tc_post(2, tc_app(A, (Term[1]){ tc_app(Q, (Term[1]){ tc_app(K0, NULL) }) }));
    Term k0 = tc_app(K0, NULL);
    Occ d1 = tc_post(1, tc_app(RD, (Term[1]){ tc_app(RQ, &k0) })), d2 = tc_post(2, tc_app(RD, (Term[1]){ tc_app(RQ, &k0) }));
    Occ rq = tc_post(3, req(w(2), w(9))), rq2 = tc_post(3, req(w(10), w(9))), rq3 = tc_post(3, req(w(60), w(9)));   /* 10+3 = 13 */
    Occ z = tc_post(2, val(w(3))), z50 = tc_post(2, val(w(50)));
    SETUP(D >= 0 && v2 && v1 && a1 && a2 && d1 && d2 && rq && rq2 && rq3 && z && z50);
    tc_seal();
    HOLDS(!tc_publishers(2, &prod, 1), "the producer sets close at the seal");
    int got[4];
    HOLDS(tc_space_publishers(1, got, 4) == 2 && got[0] == prod && got[1] == prodk && tc_space_publishers(2, got, 4) == -1,
          "tc_space_publishers lists the producers, and -1 for a space without a set");
    HOLDS(tc_rule_barred(rogue) && !tc_rule_barred(prod), "every rule outside the producer set is barred");
    /* direct writes */
    HOLDS(!tc_post(1, out3(w(1), w(1), w(1))) && !tc_post_at(tc_space_term(1), out3(w(1), w(1), w(1)), false) &&
          !tc_flat_make(1, (uint32_t)Out, (uint16_t)F, 3, (Term[3]){ w(1), w(1), w(1) }) &&
          !tc_flat_put(0, 1, Out, (Term[3]){ w(1), w(1), w(1) }) && !tc_flat_out(0, 1, Out, (Term[3]){ w(1), w(1), w(1) }),
          "no post, located post or flat write enters the evidence space");
    /* derived rules after the seal */
    ctx(1);
    tc_lemma(1, 1); tc_lemma_hyp(val(tc_v(0)));
    HOLDS(tc_lemma_end(-1) < 0, "a derived rule into an evidence space is refused after the seal");
    tc_lemma(1, 2); tc_lemma_hyp(val(tc_v(0)));
    HOLDS(tc_lemma_end(-1) >= 0, "the same derived rule into a protected space without a producer set is installed");
    /* conversion, active and rho steps */
    Conv unf = { .kind = CV_UNFOLD, .con = D, .kid = &(Conv){ .kind = CV_REFL } };
    Conv back = { .kind = CV_SYM, .kid = &unf };
    Term dv = tc_app(D, (Term[1]){ w(3) });
    HOLDS(tc_convert(v1, &back, dv) == 0, "a conversion does not rewrite an evidence fact");
    HOLDS(tc_convert(v2, &back, dv) != 0, "the same conversion rewrites a fact of a protected space without producers");
    HOLDS(tc_active_step_occ(a1) == 0 && tc_active_step_occ(a2) != 0, "an active step does not rewrite an evidence fact, elsewhere it does");
    HOLDS(tc_rho_step_occ(d1) == 0 && tc_rho_step_occ(d2) != 0, "a rho step does not rewrite an evidence fact, elsewhere it does");
    /* the producers, their refusals and the atomicity of each on every route (prodk keeps its request:
       the route tc_flat_fire carries no takes) */
    Occ hi = 64;
    for (int i = 0; i < NROUTES; i++)
        for (int kept = 0; kept < 2; kept++) {
            if (!kept && ROUTES[i].r == r_flat) continue;
            char what[200];
            const char *how = kept ? "keeping its request" : "taking its request";
            int rule = kept ? prodk : prod;
            Snap s0; snap(&s0, hi);
            unsigned long calls0 = add_calls;
            Occ q2[2] = { rq2, z }, q3[2] = { rq3, z50 }, q1[2] = { rq, z };
            Occ o = kept ? ROUTES[i].r((Fire){ NULL, q2, NULL, rule }) : ROUTES[i].r((Fire){ &q2[0], &q2[1], NULL, rule });
            snprintf(what, sizeof what, "%s, %s: an operation with no value refuses after add ran, and nothing changes", ROUTES[i].name, how);
            HOLDS(o == 0 && add_calls == calls0 + 1 && same(&s0, hi), what);
            o = kept ? ROUTES[i].r((Fire){ NULL, q3, NULL, rule }) : ROUTES[i].r((Fire){ &q3[0], &q3[1], NULL, rule });
            snprintf(what, sizeof what, "%s, %s: a guard failing after every operation ran refuses, and nothing changes", ROUTES[i].name, how);
            HOLDS(o == 0 && add_calls == calls0 + 2 && same(&s0, hi), what);
            Term bind[6] = { 0, 0, 0, 0, 0, w(10) };
            o = kept ? ROUTES[i].r((Fire){ NULL, q1, bind, rule }) : ROUTES[i].r((Fire){ &q1[0], &q1[1], bind, rule });
            snprintf(what, sizeof what, "%s, %s: a caller binding of a computed output refuses before any call, and nothing changes", ROUTES[i].name, how);
            HOLDS(o == 0 && add_calls == calls0 + 2 && same(&s0, hi), what);
            o = ROUTES[i].r((Fire){ NULL, q1, NULL, rogue });
            snprintf(what, sizeof what, "%s: a rule outside the producer set does not commit, and nothing changes", ROUTES[i].name);
            HOLDS(o == 0 && add_calls == calls0 + 2 && same(&s0, hi), what);
        }
    Occ tk2[1] = { rq2 }, kz[1] = { z }, tk3[1] = { rq3 }, kz50[1] = { z50 }, tk[1] = { rq }, kq[2] = { rq, z };
    HOLDS(r_eval_only((Fire){ tk2, kz, NULL, prod }) == TC_PREP_FN_GUARD && r_eval_only((Fire){ tk3, kz50, NULL, prod }) == TC_PREP_FN_GUARD,
          "tc_eval_prepared_ex evaluation-only: TC_PREP_FN_GUARD for no value and for a failed guard");
    HOLDS(r_eval_only((Fire){ NULL, kq, NULL, rogue }) == TC_PREP_PUBLISH_GUARD, "tc_eval_prepared_ex evaluation-only: TC_PREP_PUBLISH_GUARD for a barred rule");
    Occ made = tc_fire(prod, tk, kz, NULL);
    HOLDS(made && tc_term(made) == out3(w(2), w(9), w(10)) && !tc_alive(rq), "the producer computes Out(2, 9, 2*(2+3)) and takes its request");
    /* tc_search_reach: the kernel chooses the premises (the caller supplies no word); only producers commit */
    Term seeds[3] = { tc_space_term(1), tc_space_term(2), tc_space_term(3) };
    Occ rq1 = tc_post(3, req(w(1), w(9)));
    Snap s1; snap(&s1, hi);
    unsigned long calls2 = add_calls;
    HOLDS(rq1 && tc_search_reach(rogue, seeds, 3) == 0 && add_calls == calls2 && same(&s1, hi),
          "tc_search_reach: a rule outside the producer set commits nothing, and nothing changes");
    Occ found = tc_search_reach(prod, seeds, 3);
    HOLDS(found && tc_term(found) == out3(w(1), w(9), w(8)) && !tc_alive(rq1),
          "tc_search_reach: the kernel finds the producer's premises and commits the computed Out(1, 9, 2*(1+3))");
    /* inputs are words: an unknown in a word position has no word */
    Term m = tc_meta();
    Occ rm = tc_post(3, req(m, w(9)));
    Occ tkm[1] = { rm };
    unsigned long calls1 = add_calls;
    HOLDS(rm && tc_fire(prod, tkm, kz, NULL) == 0 && add_calls == calls1, "a matched hole holding an unknown is not a word: refused before any call");
}

static void slot_mode_controls(void) {
    printf("slot mode\n");
    theory();
    tc_protect(2);
    Occ u = tc_post(0, val(w(0)));
    HOLDS(u && tc_publishers(2, NULL, 0), "an evidence space without producers");
    tc_unset(u);
    HOLDS(!tc_alive(u + 100), "tc_unset is refused while an evidence space exists (no copies of the default appear)");
    theory();
    tc_protect(2);
    Occ v = tc_post(0, val(w(0)));
    tc_unset(v);
    HOLDS(v && tc_alive(v + 100), "(control: without an evidence space tc_unset enters slot mode)");
    HOLDS(!tc_publishers(2, NULL, 0), "tc_publishers is refused in slot mode");
}

int main(void) {
    registry_controls();
    word_sort_controls();
    rule_shape_controls();
    range_controls();
    derived_controls();
    evidence_controls();
    slot_mode_controls();
    printf("admission_kernel: %s (%d violated, %d scenes not set up)\n", violations || setups ? "VIOLATED" : "holds", violations, setups);
    return violations ? 1 : setups ? 2 : 0;
}
