/* k35: a hole of a sort takes a term of that sort, and an unknown is not yet one (the design the unit
   test pins at test_tcalc.c:82, "a := $z is not yet a wff"). A fact A1(U) with U unbound does not fire
   A1(x) |- W1(x); after a tell binds U, the same occurrence fires and makes W1 of the bound value.
   A refused attempt leaves U as it was. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule r = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };
  int rid = tc_rule(&r);
  SETUP(rid >= 0);
  Term u = tc_meta();
  SETUP(u);
  Term au = kc_u(A1c, u);                                /* places u in a NAT argument */
  SETUP(au);
  Occ o = tc_post(1, au);
  SETUP(o);
  tc_protect(1); tc_seal();
  HOLDS(tc_fire(rid, NULL, &o, NULL) == 0, "A1(U) with U unbound does not fire A1(x) |- W1(x)");
  HOLDS(tc_deref(u) == u, "the refused firing leaves U unbound");
  Term two = kc_num(2);
  SETUP(tc_tell(u, two));
  Occ w = tc_fire(rid, NULL, &o, NULL);
  HOLDS(w && tc_term(w) == kc_u(W1c, two), "after U := 2 the same occurrence makes W1(2)");
  FINISH("k35_unknown_in_sorted_hole");
}
