#pragma once
/* tc0: a prototype of the tier-0 step of the transform calculus, the fragment Micromath runs on.
   The calculus is defined in the Lean development; this is an executable sketch of one fragment.

   Terms are hash-consed: a Term is an index, and equal terms have equal indices.  Atoms come in
   two kinds, in disjoint id spaces:
   - generative names, made only by tc0_mint (a counter).  A name exists once it is minted, and no
     caller can hold one before that, so a freshly minted name is new to the whole state;
   - structural codes, tc0_code(n) for any 64-bit n.  They need no minting: the code is the term.
   Applications c(t1, ..., tn) of a declared constructor are structural as well.

   A rule keeps up to four premises (facts it reads, never consumes), may mint one fresh name, and
   makes one fact.  Premises and conclusion are flat: a constructor applied to holes and atoms.  A
   hole is bound by matching a premise (a hole that occurs twice must match equal terms), or it is
   the fresh hole, or the caller gives its value; a hole may be restricted to generative names.

   The store is a table of slots, each holding one fact; a slot never written holds the default
   fact, which the theory derives with one of its rules.  tc0_fire reads the premises from slots
   and, if the rule applies, writes its conclusion into the destination slot.  A firing that does
   not apply changes nothing: not the slots, not the name counter.  tc0_put writes a fact the caller
   vouches for (an axiom).  After tc0_seal no rule or constructor can be added. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uint32_t Term;                      /* 0 = no term */
enum { TC0_HOLES = 16, TC0_KEEPS = 4, TC0_ARITY = 8 };
enum { TC0_ANY = 0, TC0_GEN_ONLY = 1 };     /* what a hole accepts */
enum { TC0_K_GEN = 1, TC0_K_CODE = 2, TC0_K_HOLE = 3, TC0_K_APP = 4 };

bool     tc0_init(uint64_t max_slots);      /* resets everything */
int      tc0_con(int arity);                /* a new constructor, or -1 */
Term     tc0_mint(void);                    /* a new generative name, or 0 when the counter is spent */
Term     tc0_gen(uint64_t id);              /* the generative name id if it is minted, else 0 */
Term     tc0_code(uint64_t n);              /* the structural code n */
Term     tc0_hole(int i);                   /* rule variable i, for writing rules */
Term     tc0_app(int con, const Term *args);
uint64_t tc0_last_gen(void);                /* the id of the last minted name (ids start at 0) */
int      tc0_kind(Term t);                  /* TC0_K_*, or 0 if t is not a term */
uint64_t tc0_id(Term t);                    /* the id of a generative name or a code */
const Term *tc0_args(Term t, int *con, int *arity);   /* the arguments of an application, or NULL */

int  tc0_rule(int nkeep, const Term *keep, Term make, int fresh, const uint8_t *hole_kind);
bool tc0_default(int rule, const Term *in); /* the fact of an unwritten slot: this rule's conclusion */
void tc0_seal(void);
Term tc0_slot(uint64_t s);                  /* the fact in slot s (the default if never written) */
bool tc0_put(uint64_t s, Term fact);
bool tc0_fire(int rule, const uint64_t *keep, const Term *in, uint64_t dest);
