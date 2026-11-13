/* k07: keep leaves the fact, and a firing removes only what it takes.
   tc_flat_fire with a destination overwrites an existing occurrence of the same constructor and
   space in place; an absent guard elsewhere then sees a store that no sequence of takes produced.
   Second part: after the in-place overwrite the absent shortcut misses the overwritten fact. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule copy = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = -1 };   /* A1(x) |- B1(x) */
  Rule neg = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .nabsent = 1, .absent = { { kc_u(B1c, kc_num(7)), 1 } },
               .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };                                                       /* A1(x), absent B1(7) |- W1(x) */
  Rule neg2 = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .nabsent = 1, .absent = { { kc_u(B1c, tc_v(0)), 1 } },
                .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };                                                      /* A1(x), absent B1(x) |- W1(x) */
  int rc = tc_rule(&copy), rn = tc_rule(&neg), rn2 = tc_rule(&neg2);
  SETUP(rc >= 0 && rn >= 0 && rn2 >= 0);
  Term one = kc_num(1), seven = kc_num(7);
  Occ oa = tc_post(1, kc_u(A1c, one)), ob7 = tc_post(1, kc_u(B1c, seven));
  SETUP(oa && ob7);
  tc_protect(1); tc_seal();
  HOLDS(tc_fire(rn, NULL, &oa, NULL) == 0, "absent B1(7) is false while B1(7) is in the store");
  Occ o = tc_flat_fire(rc, &oa, NULL, ob7);              /* destination: the occurrence holding B1(7) */
  SETUP(o);
  HOLDS(!(o == ob7), "a firing with no take does not replace an existing occurrence");
  HOLDS(tc_alive(ob7) && tc_term(ob7) == kc_u(B1c, seven), "B1(7) is still in the protected store after a keep-only firing");
  Occ w = tc_fire(rn, NULL, &oa, NULL);
  HOLDS(w == 0, "absent B1(7) is still false: no rule took B1(7)");
  /* B1(1) is now present (in the overwritten slot). absent B1(1) must be false. */
  bool b1_present = false;
  for (Occ q = 1; q < 64; q++) if (tc_alive(q) && tc_term(q) == kc_u(B1c, one)) b1_present = true;
  SETUP(b1_present);
  Occ w2 = tc_fire(rn2, NULL, &oa, NULL);
  HOLDS(w2 == 0, "absent B1(1) is false while B1(1) is in the store");
  FINISH("k07_flat_dest_overwrite");
}
