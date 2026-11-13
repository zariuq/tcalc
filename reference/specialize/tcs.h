/* tcs.h: firing schemas (rules as data) over tcalc_ref, their text form, and their instances.
 *
 * A schema is a firing with holes.  Its terms are tr_terms of a context in which
 *   LOCAL 0 .. nparams-1        are the parameters: ground terms the caller gives at each use;
 *   LOCAL nparams .. nlocals-1  are the firing's own locals;
 *   FRESH j                     is the j-th name the firing mints.
 * The instance inst(R, params, occs) is the tr_firing of tcalc_ref.h with each parameter written in
 * for its local, the other locals renumbered from 0, and the occurrences `occs` (the takes, then
 * the reads, in the schema's order) as the identities the firing selects.  Everything the step
 * decides about an instance is decided by tcalc_ref; this file only writes instances.
 *
 * Text form, one statement per line (`#` starts a comment):
 *   theory NAME                    rule NAME ... end            (rules belong to the last theory)
 *   params A B ...                 (first in a rule: A is LOCAL 0, B is LOCAL 1, ...)
 *   locals C D ...                 (after params: C is the next local, then D, ...; optional, it
 *                                   fixes the numbering, which is otherwise by first appearance)
 *   fresh N
 *   take P    read P    make L
 *   tell T = U    apart T = U      (an equation; a disequation told)
 *   ask T = U    absent P    count P = N    host NAME(T, ...)   (guards)
 * A host guard is a predicate the program registers under NAME (tcs_register_hosts); it is
 * decided at every solution, as tcalc_ref's TR_G_HOST is, and is given its terms as written in the
 * firing.
 * Terms are read by tr_read: X (a local), _ (a new local), 12, @3 (name 3), #0 (fresh name 0),
 * f(t, ...) or a (symbols).
 */
#ifndef TCS_H
#define TCS_H

#include "../tcalc_ref.h"

typedef enum { TCS_ASK, TCS_ABSENT, TCS_COUNT, TCS_HOST } tcs_guard_kind;
typedef struct {
  tcs_guard_kind kind;
  tr_term a, b;  /* ASK: a = b; ABSENT, COUNT: the pattern a; HOST: NAME(args) */
  size_t number; /* COUNT */
} tcs_guard;

/* Host predicates: 1 holds at every solution, 0 fails at some solution, -1 no verdict.  args are
 * the guard's terms as written in the firing; read them through the view. */
typedef int (*tcs_host_fn)(tr_view *view, const tr_term *args, size_t nargs);
typedef struct {
  const char *name;
  tcs_host_fn fn;
} tcs_host;
void tcs_register_hosts(const tcs_host *hosts, size_t n); /* replaces the registry */
tcs_host_fn tcs_host_find(const char *name);

typedef struct {
  char *name;
  uint32_t nparams, nlocals, fresh;
  tr_term *takes, *reads, *makes;
  size_t ntakes, nreads, nmakes;
  tr_eq *tells, *apart;
  size_t ntells, napart;
  tcs_guard *guards;
  size_t nguards;
} tcs_rule;

typedef struct {
  char *name;
  tcs_rule *rules;
  size_t nrules;
} tcs_theory;

/* Reads every theory of `text` into the context.  Returns how many were read and sets *out, or
 * returns -1 and writes a message naming the line into err. */
int tcs_read(tr_ctx *c, const char *text, tcs_theory **out, char *err, size_t errlen);
void tcs_free(tcs_theory *theories, int n);
const tcs_rule *tcs_find(const tcs_theory *t, const char *rule);

/* ---- rules as the reference's own data ----
 * A tr_firing is a schema when its LOCAL 0 .. nparams-1 stand for the parameters.  The occurrences
 * of its takes and reads are ignored (each decision supplies them), its makes ask for fresh
 * identities (id 0) and make no stored schema (schema_locals 0), and its guards are EQUAL, ABSENT,
 * COUNT, or HOST guards that name a registered host: entailed = tcs_named_host, env = a
 * tcs_host_ref.  Such a firing, instantiated, is also an ordinary firing of tcalc_ref. */
typedef struct {
  const char *name;    /* a host registered with tcs_register_hosts */
  const tr_term *args; /* its terms, as written in the firing */
  size_t nargs;
} tcs_host_ref;
int tcs_named_host(tr_view *view, void *env); /* calls the registered host named by env */

/* The rule `name` of schema f: true, or false with a message in err when f is no schema. */
bool tcs_rule_from_firing(tr_ctx *c, const char *name, const tr_firing *f, uint32_t nparams, tcs_rule *out,
                          char *err, size_t errlen);
/* A theory of n rules (names[i], firings[i], nparams[i]); NULL with a message when one is no schema.
 * Free it with tcs_free(theory, 1). */
tcs_theory *tcs_theory_from_firings(tr_ctx *c, const char *name, size_t n, const char *const *names,
                                    const tr_firing *firings, const uint32_t *nparams, char *err, size_t errlen);
/* Writes theories in the text form, which tcs_read reads back to the same rules (same terms, same
 * local numbering).  Symbol names must be lowercase identifiers; returns false otherwise. */
bool tcs_write(FILE *out, const tr_ctx *c, const tcs_theory *theories, int n);

/* An instance.  It owns its arrays and is reused: tcs_instance_of writes the instance of `r`
 * into it, growing it when needed.  Parameters must be terms of the context. */
typedef struct tcs_hostenv tcs_hostenv;
typedef struct {
  tr_firing firing;
  tr_use *uses;
  tr_make *makes;
  tr_eq *eqs;
  tr_guard *guards;
  tcs_hostenv *hosts; /* one per guard */
  size_t cap_uses, cap_makes, cap_eqs, cap_guards;
} tcs_instance;

const tr_firing *tcs_instance_of(tcs_instance *in, tr_ctx *c, const tcs_rule *r, const tr_term *params,
                                 const tr_occ *occs);
void tcs_instance_free(tcs_instance *in);

/* The generated code's interface (tcs_gen writes it; drivers read it). */
typedef tr_verdict (*tcs_decide_fn)(tr_state *s, const tr_term *params, const tr_occ *occs, tr_result *r,
                                    bool commit);
typedef struct {
  const char *name;
  tcs_decide_fn decide; /* commit = false: tr_admits; true: tr_fire */
  bool specialized;     /* false: the rule is outside the fragment and its code is the generic route */
  uint32_t nparams;
  size_t ntakes, nreads;
} tcs_compiled_rule;

typedef struct {
  const char *name;
  bool (*link)(tr_ctx *c);           /* interns the theory's symbols and constants into c */
  const tcs_theory *(*schemas)(void); /* the theory as data, read into the linked context */
  size_t nrules;
  const tcs_compiled_rule *rules;
} tcs_compiled_theory;

/* Defined by a file tcs_gen wrote: every theory it compiled, and how many decisions took the
 * specialized path or the generic route. */
extern const tcs_compiled_theory tcs_compiled[];
extern const size_t tcs_ncompiled;
typedef struct {
  size_t fast, generic;
} tcs_counts;
extern tcs_counts tcs_count;
/* How many symbols of the context get another head key from the generated code than from
 * tcalc_ref's head_key (0 when the two agree). */
size_t tcs_head_keys_differ(tr_ctx *c);

#endif
