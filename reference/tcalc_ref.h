/* tcalc_ref.h: a reference implementation of one step of the transform calculus.
 *
 * The definition is the Lean development ConstraintMultisetRewriting (namespace Interface and
 * its first-order, disequation and contextual instances). Every part below names the
 * definition it implements.
 *
 *   state   = a frame (declared variables, minted names, disequations), its knowledge, and the
 *             present occurrences                                   (EffectCore.frame/knowledge/present)
 *   firing  = an extension (fresh variables and fresh names), a selection (takes, reads, makes),
 *             information (the take and read equations and the tells), told disequations, and
 *             guards                                                 (EffectCore, Disequality.Firing)
 *   admits  = shapes, the selection fits the present occurrences, the information is solvable at
 *             the target frame, and every guard holds at every solution of the information
 *                                                                    (Step.Standard.admits_iff)
 *   result  = present occurrences fired (fire), the frame extended and then settled along the
 *             most general unifier, the knowledge the information applied along the settlement
 *                                                                    (Step.Standard.knowledge_preparedResult)
 *
 * Nothing is scheduled here: which firing to try, and in what order, is the caller's control.
 * A refused firing changes nothing.  A context and its states are used by one thread at a time,
 * and a guard's callbacks only read through their view.
 */
#ifndef TCALC_REF_H
#define TCALC_REF_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

/* ---------------------------------------------------------------------------------------------
 * Terms: first-order terms over a declared signature, hash-consed (equal terms have equal ids).
 *
 *   APP    a declared symbol of fixed arity applied to that many terms (constants: arity 0)
 *   CODE   a structural code: a 64-bit value; needs no minting, and its id is computed from it
 *   NAME   a generative name: meaningful only once minted by a frame extension (a fresh firing)
 *   VAR    a variable of the frame (a metavariable that solutions instantiate)
 *   LOCAL  in a firing: the firing's i-th fresh variable; in a stored schema: its i-th private
 *          variable, opened at a fresh scope by every port that selects it
 *   FRESH  in a firing: the j-th name this firing mints
 * NAME and CODE are disjoint kinds: the name 0 is not the code 0.
 * ------------------------------------------------------------------------------------------- */

typedef uint32_t tr_term;
#define TR_NONE ((tr_term)0) /* never a term */

typedef enum { TR_APP, TR_CODE, TR_NAME, TR_VAR, TR_LOCAL, TR_FRESH } tr_kind;

typedef struct tr_ctx tr_ctx; /* the term table and the signature; shared by states */

tr_ctx *tr_ctx_new(void);
void tr_ctx_free(tr_ctx *ctx);
size_t tr_ctx_terms(const tr_ctx *ctx); /* terms in the table (it only grows) */

/* Declares (or finds) the symbol name/arity; symbols with one name and two arities differ. */
uint32_t tr_symbol(tr_ctx *ctx, const char *name, uint32_t arity);
const char *tr_symbol_name(const tr_ctx *ctx, uint32_t symbol);
uint32_t tr_symbol_arity(const tr_ctx *ctx, uint32_t symbol);

tr_term tr_app(tr_ctx *ctx, uint32_t symbol, const tr_term *args);
tr_term tr_const(tr_ctx *ctx, const char *name); /* a symbol of arity 0 */
tr_term tr_code(tr_ctx *ctx, int64_t value);
tr_term tr_name(tr_ctx *ctx, uint32_t index);
tr_term tr_var(tr_ctx *ctx, uint32_t index);
tr_term tr_local(tr_ctx *ctx, uint32_t index);
tr_term tr_fresh(tr_ctx *ctx, uint32_t index);

tr_kind tr_term_kind(const tr_ctx *ctx, tr_term t);
uint32_t tr_term_symbol(const tr_ctx *ctx, tr_term t);    /* APP */
uint32_t tr_term_arity(const tr_ctx *ctx, tr_term t);     /* APP: number of arguments */
tr_term tr_term_arg(const tr_ctx *ctx, tr_term t, uint32_t i);
int64_t tr_term_code(const tr_ctx *ctx, tr_term t);       /* CODE */
uint32_t tr_term_index(const tr_ctx *ctx, tr_term t);     /* NAME, VAR, LOCAL, FRESH */

/* A tiny reader for tests.  Syntax: 12, -3 (codes); f(t, ...) or a (symbols); X, Head (locals,
 * numbered by first appearance in the scope); _ (a new local each time); $3 (variable 3);
 * @3 (name 3); #3 (fresh name 3 of the firing).  Returns TR_NONE on a syntax error. */
typedef struct tr_scope tr_scope;
tr_scope *tr_scope_new(void);
void tr_scope_free(tr_scope *scope);
uint32_t tr_scope_size(const tr_scope *scope); /* locals named so far */
tr_term tr_read(tr_ctx *ctx, tr_scope *scope, const char *text);
void tr_print(FILE *out, const tr_ctx *ctx, tr_term t);

/* ---------------------------------------------------------------------------------------------
 * States (EffectCore.frame, knowledge, present).
 *
 * The frame declares variables 0 .. vars-1 and has minted names 0 .. names-1, and it carries
 * disequations (Disequality.Frame).  Settlement along the most general unifier is kept as
 * bindings of variables: a bound variable has left the frame, and every term is read through
 * the bindings (tr_resolve).  The knowledge at a reached frame is the information applied along
 * its settlement, which is a list of identities; they are not stored (the empty store has
 * exactly their solutions, Frames.Equivalent).
 * ------------------------------------------------------------------------------------------- */

typedef uint64_t tr_occ; /* an occurrence identity; 0 is never an identity */
typedef struct tr_state tr_state;

tr_state *tr_state_new(tr_ctx *ctx);
tr_state *tr_state_clone(const tr_state *s);
void tr_state_free(tr_state *s);
tr_ctx *tr_state_ctx(const tr_state *s);

/* Same frame, bindings, disequations, present occurrences (in order) and identity counter. */
bool tr_state_equal(const tr_state *a, const tr_state *b);

uint32_t tr_vars(const tr_state *s);    /* variables declared so far */
uint32_t tr_names(const tr_state *s);   /* names minted so far */
size_t tr_present_count(const tr_state *s);
/* Iteration in the order occurrences were made: `after` = 0 gives the first; 0 ends.  The
 * label is the label at the state's frame.  The state must not change during an iteration. */
tr_occ tr_next_present(const tr_state *s, tr_occ after, tr_term *label);
/* The same, restricted to the occurrences whose label can equal `pattern` by its head (the
 * head index): those with the pattern's head, then those whose head is still open; every
 * occurrence when the pattern's head is open.  For control layers that match. */
tr_occ tr_next_candidate(const tr_state *s, tr_term pattern, tr_occ after, tr_term *label);
bool tr_present(const tr_state *s, tr_occ id, tr_term *label); /* a stored schema as stored */
tr_term tr_resolve(const tr_state *s, tr_term t); /* t at the state's frame */
bool tr_bound(const tr_state *s, uint32_t var);
size_t tr_apart_count(const tr_state *s); /* disequations of the frame not yet decided */

/* ---------------------------------------------------------------------------------------------
 * Firings.  Terms of a firing live at its target frame: the state's frame (VAR, NAME, codes and
 * symbols) extended by `locals` fresh variables (LOCAL i) and `fresh` new names (FRESH j)
 * (EffectCore.extension).  A take or read of a stored schema opens the schema's private
 * variables at that port's own fresh scope (ContextualActivatedStep, ResolutionReadPort).
 * The settlement is written into the result: the made labels, the bindings and the told
 * disequations are kept resolved, and a local still unbound becomes a new frame variable.
 * ------------------------------------------------------------------------------------------- */

typedef struct { tr_term pattern; tr_occ occ; } tr_use;          /* pattern = label of occ */
typedef struct { tr_term left, right; } tr_eq;
typedef struct {
  tr_term label;
  tr_occ id;              /* 0: the step gives a fresh identity; otherwise it must be fresh */
  uint32_t schema_locals; /* > 0: a stored schema whose LOCAL 0 .. n-1 are its private variables */
} tr_make;

/* Guards: predicates on the solutions of the information (Step.Standard.Holds).  A guard is
 * admitted when it holds at EVERY solution that separates the frame's disequations
 * (Frames.Entails, Disequality.entails_iff), never only at the most general unifier. */
typedef struct tr_view tr_view; /* the information of a firing under trial */
typedef enum { TR_OUT = 0, TR_IN = 1, TR_DEPENDS = 2 } tr_member;
typedef enum {
  TR_G_EQUAL,  /* an ask: a = b                                            (Check.equal) */
  TR_G_ABSENT, /* no present occurrence's label equals pattern a           (Check.absent) */
  TR_G_COUNT,  /* exactly `number` present labels equal pattern a          (Check.count) */
  TR_G_QUERY,  /* the region's present occurrences are exactly `seen`      (PredicateQuery.Holds) */
  TR_G_HOST    /* any predicate; the host decides it at every solution     (Step.Standard.Holds) */
} tr_guard_kind;
typedef struct {
  tr_guard_kind kind;
  tr_term a, b;
  size_t number;
  /* QUERY: membership of one present occurrence, given its label at the most general unifier:
   * IN or OUT when the same at every solution, DEPENDS when solutions disagree. */
  tr_member (*region)(tr_view *view, tr_term label, void *env);
  const tr_occ *seen;
  size_t nseen;
  /* HOST: 1 holds at every solution, 0 fails at some solution, -1 no verdict. */
  int (*entailed)(tr_view *view, void *env);
  void *env;
} tr_guard;

typedef struct {
  uint32_t locals, fresh;                 /* the extension */
  const tr_use *takes;   size_t ntakes;   /* the selection (Selection.taken/read/made) */
  const tr_use *reads;   size_t nreads;
  const tr_make *makes;  size_t nmakes;
  const tr_eq *tells;    size_t ntells;   /* the information (Selection.problem) */
  const tr_eq *apart;    size_t napart;   /* told disequations (Disequality.Firing.tells) */
  const tr_guard *guards; size_t nguards;
} tr_firing;

typedef enum { TR_ADMITTED, TR_REFUSED, TR_NO_VERDICT } tr_verdict;
typedef enum { TR_OK, TR_SHAPES, TR_FITS, TR_UNSOLVABLE, TR_GUARD } tr_reason;

typedef struct {
  tr_verdict verdict;
  tr_reason reason;  /* the first conjunct of admits_iff that failed */
  size_t guard;      /* TR_GUARD: the guard that failed */
  tr_occ *made;      /* optional, room for nmakes: the identities made, in make order */
  tr_term *locals;   /* optional, room for `locals`: each local at the result frame (its value,
                        or the new variable it became when left unbound) */
  uint32_t first_name; /* on admission: FRESH j became name first_name + j */
} tr_result;

/* Decides admission (Step.Standard.admits_iff) and changes nothing. */
tr_verdict tr_admits(tr_state *s, const tr_firing *f, tr_result *r);
/* Decides admission; when admitted, the state becomes the result (Step.result). */
tr_verdict tr_fire(tr_state *s, const tr_firing *f, tr_result *r);
/* A run (Step.Run): fires in order and stops at the first firing not admitted; returns how
 * many were admitted. */
size_t tr_run(tr_state *s, const tr_firing *firings, size_t n);

/* The view a QUERY region or HOST guard reads.  Terms are written as in the firing. */
tr_ctx *tr_view_ctx(const tr_view *v);
tr_term tr_view_resolve(tr_view *v, tr_term t);          /* t at the most general unifier */
bool tr_view_ground(tr_view *v, tr_term t);              /* the same term at every solution */
bool tr_view_same(tr_view *v, tr_term a, tr_term b);     /* equal at every solution */
bool tr_view_possible(tr_view *v, tr_term a, tr_term b); /* equal at some solution */
bool tr_view_code(tr_view *v, tr_term t, int64_t *value);/* t is the same code at every solution */
tr_occ tr_view_next_present(tr_view *v, tr_occ after, tr_term *label); /* labels at theta */

#endif
