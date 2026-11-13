/* k20: the flat entry point and the general entry point agree on the result.
   (a) tc_flat_fire on a rule that falls through to the general path posts the made fact through
       tc_fire and then stores a second copy: one firing, two facts.
   (b) tc_flat_fire on a make-only rule with extra makes writes the first make and drops the rest
       (and accepts a candidate whose extra make has an unbound hole).
   Found by the random differential (classes "store via tc_flat_fire"). */
#include "kc.h"

static int count_live(Term t, int space) {
  int n = 0; Term sp = tc_space_term((uint8_t)space);
  for (Occ o = 1; o < 256; o++) if (tc_alive(o) && tc_occ_space(o) == sp && tc_term(o) == t) n++;
  return n;
}

int main(void) {
  kc_theory();
  kc_ctx_nat(2);
  Rule spend = { .ntake = 1, .take = { { kc_u(W1c, tc_v(0)), 2 } }, .make = { kc_u(W1c, tc_v(0)), 3 }, .fresh = -1 };   /* makes the store a multiset */
  Rule mint = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .nabsent = 1, .absent = { { kc_u(B1c, tc_v(0)), 1 } },
                .make = { kc_u(W1c, tc_v(0)), 2 }, .fresh = -1 };                                                     /* A1(x), absent B1(x) |- W1(x)@2 */
  Rule both = { .make = { kc_u(A1c, tc_v(0)), 3 }, .nmake_extra = 1, .make_extra = { { kc_u(B1c, tc_v(1)), 3 } }, .fresh = -1, .inputs = 0x3 };  /* |- A1(x)@3, B1(y)@3 */
  int rs = tc_rule(&spend), rm = tc_rule(&mint), rb = tc_rule(&both);
  SETUP(rs >= 0 && rm >= 0 && rb >= 0);
  Term one = kc_num(1), two = kc_num(2);
  Occ oa = tc_post(1, kc_u(A1c, one));
  SETUP(oa);
  tc_protect(1); tc_protect(2); tc_protect(3); tc_seal();
  Occ g = tc_fire(rm, NULL, &oa, NULL);
  SETUP(g && count_live(kc_u(W1c, one), 2) == 1);
  Occ f = tc_flat_fire(rm, &oa, NULL, 0);
  SETUP(f);
  int n = count_live(kc_u(W1c, one), 2);
  HOLDS(n == 2, "one tc_fire and one tc_flat_fire of the same rule leave two W1(1), one each");
  printf("    live W1(1) in space 2 after tc_fire + tc_flat_fire: %d\n", n);
  Term in_both[2] = { one, two };
  Occ b = tc_flat_fire(rb, NULL, in_both, 0);
  SETUP(b);
  HOLDS(count_live(kc_u(B1c, two), 3) == 1, "tc_flat_fire of a two-make rule makes the second fact too");
  Term in_half[2] = { one, 0 };
  HOLDS(tc_fire(rb, NULL, NULL, in_half) == 0, "tc_fire refuses the two-make rule when the second make's hole is unbound");
  HOLDS(tc_flat_fire(rb, NULL, in_half, 0) == 0, "tc_flat_fire refuses it too");
  FINISH("k20_flat_fire_general_path");
}
