/* Micromath as a theory over tc0.
   Its symbols, decided from Micromath's own rules (the reference kernel): the projections X = 0 and
   Y = 1 and every symbol made by new_node_opaque or new_node_def are minted, so they are generative
   names; proj1, proj2 and refl hold for any symbol whatever, so a symbol value that was never minted
   is taken as its structural code; new_node_def takes only minted symbols.  The symbol numbered n is
   the generative name n if n has been minted, otherwise the code n. */
#include "micromath.h"
#include "tc0.h"

static int EQ, r_proj1, r_proj2, r_refl, r_sub1, r_sub2, r_def;
MmEntry mm_entries[6];
enum { MAX_SLOT = 1u << 24 };

static Term sym(uint64_t n) { Term g = tc0_gen(n); return g ? g : tc0_code(n); }
static Term eq4(Term o, Term f, Term x, Term y) { Term a[4] = { o, f, x, y }; return tc0_app(EQ, a); }

bool mm_init(void) {
  if (!tc0_init(MAX_SLOT)) return false;
  EQ = tc0_con(4);
  Term X = tc0_mint(), Y = tc0_mint();                         /* ids 0 and 1 */
  Term t = tc0_hole(0), u = tc0_hole(1), w = tc0_hole(2), x = tc0_hole(3), a = tc0_hole(4), b = tc0_hole(5),
       u1 = tc0_hole(6), w1 = tc0_hole(7), x1 = tc0_hole(8);
  r_proj1 = tc0_rule(0, NULL, eq4(x, X, x, a), -1, NULL);      /* x = X(x,a) */
  r_proj2 = tc0_rule(0, NULL, eq4(a, Y, x, a), -1, NULL);      /* a = Y(x,a) */
  r_refl  = tc0_rule(0, NULL, eq4(a, a, X, Y), -1, NULL);      /* a = a(X,Y) */
  Term s1[4] = { eq4(x, t, u, w), eq4(u1, u, a, b), eq4(w1, w, a, b), eq4(x1, x, a, b) };
  r_sub1  = tc0_rule(4, s1, eq4(x1, t, u1, w1), -1, NULL);
  Term s2[4] = { eq4(x, t, u, w), eq4(u1, u, a, b), eq4(w1, w, a, b), eq4(x1, t, u1, w1) };
  r_sub2  = tc0_rule(4, s2, eq4(x1, x, a, b), -1, NULL);
  uint8_t named_only[TC0_HOLES] = { TC0_GEN_ONLY, TC0_GEN_ONLY, TC0_GEN_ONLY };
  r_def   = tc0_rule(0, NULL, eq4(x1, t, u, w), 8, named_only); /* fresh x1 := t(u,w), t u w minted */
  MmEntry e[6] = {
    { "proj1", MM_ENT_INPUTS, r_proj1, 2, { 3, 4 } }, { "proj2", MM_ENT_INPUTS, r_proj2, 2, { 3, 4 } },
    { "refl",  MM_ENT_INPUTS, r_refl,  1, { 4 } },    { "sub1",  MM_ENT_KEEPS,  r_sub1,  0, { 0 } },
    { "sub2",  MM_ENT_KEEPS,  r_sub2,  0, { 0 } },    { "new_def", MM_ENT_FRESH, r_def, 3, { 0, 1, 2 } },
  };
  for (int i = 0; i < 6; i++) mm_entries[i] = e[i];
  Term in[TC0_HOLES] = { [3] = X, [4] = X };
  bool ok = EQ >= 0 && X && Y && r_proj1 >= 0 && r_proj2 >= 0 && r_refl >= 0 && r_sub1 >= 0 && r_sub2 >= 0 && r_def >= 0
            && tc0_default(r_proj1, in);                        /* an unwritten slot holds proj1(X, X) */
  tc0_seal();
  return ok;
}

uint64_t mm_new_opaque(void) { Term g = tc0_mint(); return g ? tc0_id(g) : 0; }
uint64_t mm_new_def(uint64_t f, uint64_t x, uint64_t y, uint64_t s) {
  Term in[TC0_HOLES] = { [0] = sym(f), [1] = sym(x), [2] = sym(y) };
  return tc0_fire(r_def, NULL, in, s) ? tc0_last_gen() : 0;
}
bool mm_set(uint64_t o, uint64_t f, uint64_t x, uint64_t y, uint64_t s) { return tc0_put(s, eq4(sym(o), sym(f), sym(x), sym(y))); }
MmBody mm_get(uint64_t s) {
  const Term *a = tc0_args(tc0_slot(s), NULL, NULL);
  return (MmBody){ tc0_id(a[0]), tc0_id(a[1]), tc0_id(a[2]), tc0_id(a[3]) };
}
bool mm_proj1(uint64_t x, uint64_t y, uint64_t s) { Term in[TC0_HOLES] = { [3] = sym(x), [4] = sym(y) }; return tc0_fire(r_proj1, NULL, in, s); }
bool mm_proj2(uint64_t x, uint64_t y, uint64_t s) { Term in[TC0_HOLES] = { [3] = sym(x), [4] = sym(y) }; return tc0_fire(r_proj2, NULL, in, s); }
bool mm_refl(uint64_t a, uint64_t s) { Term in[TC0_HOLES] = { [4] = sym(a) }; return tc0_fire(r_refl, NULL, in, s); }
bool mm_sub1(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { uint64_t p[4] = { m, u, v, x }; return tc0_fire(r_sub1, p, NULL, d); }
bool mm_sub2(uint64_t m, uint64_t u, uint64_t v, uint64_t x, uint64_t d) { uint64_t p[4] = { m, u, v, x }; return tc0_fire(r_sub2, p, NULL, d); }
