/* tcs_inside.h: the reference implementation compiled together with code specialized to it.
 *
 * Generated code decides firings on tcalc_ref's own states, so it reads the state's internals
 * (occurrence slots, head buckets, the term table).  This header includes tcalc_ref.c itself, so
 * the reference stays one unedited file; a program has exactly one translation unit that
 * includes this header (the generated file), and the rest of the program uses tcalc_ref.h.
 *
 * What generated code relies on, beyond tcalc_ref.h:
 *   ND, ARG          the term table: node kind, symbol (val) and arguments; O(1)
 *   find_slot        identity -> slot, O(1) expected (the identity map)
 *   add_occ, remove_occ   O(1): the order of making and the head bucket (exactly as decide does)
 *   head_key, bucket_of   the head index; tcs_app_key below must equal head_key on an application
 */
#ifndef TCS_INSIDE_H
#define TCS_INSIDE_H

#include "../tcalc_ref.c"
#include "tcs.h"

/* The ground fragment of a state: no frame variables, no live disequations, nothing in the open
 * bucket.  Then every present label is ground and is its own label at the frame (tr_resolve is
 * the identity on it), and matching against it is one-way. */
static inline bool tcs_ground_state(const tr_state *s) {
  return s->nvars == 0 && s->live_ds == 0 && s->bk[0].count == 0;
}

/* A parameter the fast path takes as it is: a term without variables, locals or fresh names. */
static inline bool tcs_ground_param(const tr_ctx *c, tr_term t) {
  return !(c->nodes[t].flags & (HAS_VAR | HAS_LOCAL | HAS_FRESH));
}

static inline uint32_t tcs_maxname(const tr_ctx *c, tr_term t) { return c->nodes[t].maxname; }

/* head_key of an application of symbol `sym` (tcalc_ref.c, head_key, case TR_APP). */
static inline uint64_t tcs_app_key(uint32_t sym) { return mix(11, sym) | 1; }

/* The first slot of a head bucket, or NIL. */
static inline uint32_t tcs_bucket_first(const tr_state *s, uint64_t key) {
  uint32_t b = bucket_of((tr_state *)s, key, false);
  return b == NIL ? NIL : s->bk[b].first;
}

static inline tr_verdict tcs_refuse(tr_result *r, tr_reason why, size_t guard) {
  r->verdict = TR_REFUSED;
  r->reason = why;
  r->guard = guard;
  return TR_REFUSED;
}

/* Checks tcs_app_key against head_key for every symbol of the context; 0 when they agree. */
static inline size_t tcs_inside_selfcheck(tr_ctx *c) {
  tr_state *s = tr_state_new(c);
  size_t bad = 0;
  for (size_t i = 0; i < c->nsyms; i++) {
    uint32_t n = c->syms[i].arity;
    tr_term small[8], *args = n <= 8 ? small : xrealloc(NULL, n * sizeof *args);
    for (uint32_t k = 0; k < n; k++) args[k] = tr_code(c, 0);
    bad += head_key(s, tr_app(c, (uint32_t)i, args)) != tcs_app_key((uint32_t)i);
    if (args != small) free(args);
  }
  tr_state_free(s);
  return bad;
}

#endif
