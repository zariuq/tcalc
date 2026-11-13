/* bl.h: a binder layer on tcalc_ref: terms with de Bruijn binders as first-order data, and
 * substitution as rules (explicit substitutions), so that every substitution a checker relies on
 * is a fact made by a firing of the step.
 *
 * The language is given by a binding signature: each constructor has an arity and, for each
 * argument, the number of binders it lies under (BL_DATA: the argument is data, such as a code,
 * and is not a term of the language).  The layer adds variables var(n), n a numeral z, s(z), ...
 * (var(z) is the innermost binder), and substitutions, the explicit substitutions of lambda-upsilon
 * (Lescanne) with the cons of lambda-sigma (Abadi, Cardelli, Curien, Levy):
 *
 *   id            var(n) -> var(n)
 *   sh            var(n) -> var(n+1)                    (shift)
 *   shk(k)        var(n) -> var(n+k)
 *   lf(s)         var(0) -> var(0), var(n+1) -> s(n) shifted by one    (lifting under a binder)
 *   cs(u, s)      var(0) -> u, var(n+1) -> s(n)        (u . s; u/ is cs(u, id))
 *   bot           only as the head of a cs: var(0) has no image (a forbidden variable)
 *
 * Facts (made only by the rules below, generated from the signature):
 *   ev(t, s, r)        r is t with s applied: t[s] = r
 *   mentions(t, k)     var(k) occurs free in t
 * Rules: for each constructor f, ev(f(x..), S, f(y..)) from ev(x_i, lf^{b_i}(S), y_i) for each term
 * argument (data arguments are kept); ev(t, id, t); the variable rules
 *   var(0)[cs(U,S)] = U        var(n+1)[cs(U,S)] = var(n)[S]
 *   var(0)[lf(S)] = var(0)     var(n+1)[lf(S)] = (var(n)[S])[sh]
 *   var(n)[sh] = var(n+1)      var(n)[shk(0)] = var(n)      var(n)[shk(k+1)] = var(m+1) if var(n)[shk(k)] = var(m)
 * (no rule for var(0)[cs(bot, S)]); and mentions(var(k), k), mentions(f(x..), k) from
 * mentions(x_i, k + b_i).
 *
 * The C here only chooses which rule to fire on which facts, and remembers the facts made (by
 * term); it computes no result itself.  Higher-order pattern matching (Miller) is ev with the
 * renaming bl_rho: at depth d, a pattern variable applied to the distinct bound variables
 * y_1 .. y_a has, for the term t, the solution body t[rho], rho = e_0 . ... . e_{d-1} . shk(a), with
 * e_i = var(a-1-j) when i = y_j and bot otherwise: the variables bound outside the pattern move
 * down by d and up by a (the "depth - arity" transport), and no other bound variable may occur.
 */
#ifndef BL_H
#define BL_H

#include "rk.h"

#define BL_DATA 0xffu

typedef struct {
  const char *name;
  uint32_t arity;
  const uint8_t *binders; /* arity entries: binders over each argument, or BL_DATA; NULL: none */
} bl_con;

typedef struct bl bl;

bl *bl_new(rk_engine *e, const bl_con *cons, size_t ncons);
void bl_free(bl *b);

uint32_t bl_symbol(const bl *b, size_t con); /* the tcalc symbol of constructor `con` */

tr_term bl_nat(bl *b, uint32_t n); /* s^n(z) */
bool bl_nat_value(const bl *b, tr_term t, uint32_t *n);
tr_term bl_var(bl *b, uint32_t n);
bool bl_var_index(const bl *b, tr_term t, uint32_t *n);

tr_term bl_id(bl *b);
tr_term bl_sh(bl *b);
tr_term bl_bot(bl *b);
tr_term bl_shk(bl *b, uint32_t k);
tr_term bl_lf(bl *b, tr_term s);
tr_term bl_cs(bl *b, tr_term u, tr_term s);
/* The Miller renaming for a pattern variable at depth d applied to ys[0..arity-1] (indices of
 * bound variables at that depth, distinct, each < d). */
tr_term bl_rho(bl *b, uint32_t depth, const uint32_t *ys, uint32_t arity);

/* The fact ev(t, s, r): its occurrence, made now or earlier, and r; 0 when t[s] has no value
 * (t meets a forbidden variable).  t must be a term of the language and s a substitution. */
tr_occ bl_ev(bl *b, tr_term t, tr_term s, tr_term *r);
/* The fact mentions(t, k), or 0 when var(k) does not occur free in t. */
tr_occ bl_mentions(bl *b, tr_term t, uint32_t k);

/* Patterns of the layer's facts, for the rules of a client. */
tr_term bl_ev_fact(bl *b, tr_term t, tr_term s, tr_term r);
tr_term bl_mentions_fact(bl *b, tr_term t, tr_term k);

/* 1 + the largest free variable of t, 0 when t is closed (a C summary, used only to prune). */
uint32_t bl_free_bound(bl *b, tr_term t);

/* Statistics. */
uint64_t bl_facts_made(const bl *b);

/* The layer's rules, in a fixed order (for a client that compiles them, rk_to_schema): fills up
 * to cap of them into out and returns how many there are. */
size_t bl_rules(bl *b, rk_rule **out, size_t cap);

/* Faults for harness checks (0: none): set before bl_new. */
extern int bl_fault;

#endif
