/* rk.h: rules as data over tcalc_ref's step, and the firing of a rule on given facts.
 *
 * A rule is a firing schema of tcalc_ref.h: its terms are written over locals (LOCAL i); it takes
 * and reads facts by pattern, may tell disequations apart, may carry guards, and makes facts.
 * Some locals are parameters: the caller gives their values when it fires the rule, and the step
 * binds them by equations (tells).  Every other local must be bound by unifying the patterns with
 * the facts the caller selects, so that every fact made is ground: rk_fire stops the process if a
 * firing would leave a frame variable behind (a schematic fact would be unsound here).
 *
 * The caller (a checker's work order) chooses which rule to fire on which facts; the step decides.
 * A refused firing changes nothing and rk_fire returns 0.
 */
#ifndef RK_H
#define RK_H

#include "../tcalc_ref.h"

typedef struct {
  const char *what;
  uint32_t locals, fresh;
  tr_term *takes, *reads, *makes;
  size_t ntakes, nreads, nmakes, captakes, capreads, capmakes;
  uint32_t *params; /* locals given by the caller, in order */
  size_t nparams, capparams;
  tr_eq *apart;
  size_t napart, capapart;
  tr_guard *guards;
  size_t nguards, capguards;
  int fast; /* >= 0: the index of this rule's compiled decision (see rk_engine.decide); -1: none */
} rk_rule;

void rk_init(rk_rule *r, const char *what, uint32_t locals);
void rk_take(rk_rule *r, tr_term pattern);
void rk_read(rk_rule *r, tr_term pattern);
void rk_make(rk_rule *r, tr_term label);
void rk_param(rk_rule *r, uint32_t local);
void rk_apart(rk_rule *r, tr_term a, tr_term b);
void rk_absent(rk_rule *r, tr_term pattern);
void rk_guard(rk_rule *r, tr_guard g);
void rk_free(rk_rule *r);

typedef struct {
  tr_ctx *ctx;
  tr_state *st;
  uint64_t fired, refused; /* firings admitted, refused */
  /* A compiled decision for rules with fast >= 0 (code the specializer wrote from the rule as a
   * schema, rk_to_schema): the parameters in the rule's order, the occurrences, commit.  It must
   * decide exactly what tr_fire decides on the rule's instance (the specializer's law). */
  tr_verdict (*decide)(int fast, tr_state *s, const tr_term *params, const tr_occ *occs, tr_result *r);
  uint64_t fast_decisions;
  /* scratch, reused by every firing */
  tr_use *uses;
  tr_eq *eqs;
  tr_make *mks;
  tr_occ *made;
  size_t capuses, capeqs, capmks;
} rk_engine;

void rk_engine_init(rk_engine *e, tr_ctx *ctx, tr_state *st);
void rk_engine_free(rk_engine *e);

/* Fires r: occs are the selected facts (the takes', then the reads'), vals the parameters' values.
 * Returns the first fact made (1 when r makes nothing), or 0 when the step refuses; made, when
 * not NULL, receives every fact made, in order.  *first_name, when not NULL, receives the name
 * the firing minted first. */
tr_occ rk_fire(rk_engine *e, const rk_rule *r, const tr_occ *occs, const tr_term *vals, tr_occ *made,
               uint32_t *first_name);

/* r as a schema for the specializer (specialize/tcs.h): a tr_firing whose LOCAL 0 .. nparams-1 are
 * r's parameters in order and whose other locals follow, with no tells for the parameters (each
 * decision gives them).  The arrays are allocated; free them with rk_schema_free. */
void rk_to_schema(tr_ctx *c, const rk_rule *r, tr_firing *out, uint32_t *nparams);
void rk_schema_free(tr_firing *f);

/* The label of a present fact (the process stops if it is not present). */
tr_term rk_label(rk_engine *e, tr_occ o);
/* Argument i of a fact's label. */
tr_term rk_arg(rk_engine *e, tr_occ o, uint32_t i);

#endif
