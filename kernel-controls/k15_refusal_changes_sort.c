/* k15: a refused firing leaves the state unchanged.
   Open instantiation places an unknown in a sorted constructor argument and records the sort
   without a trail entry; when the firing is then refused, the unknown stays constrained, and a
   tell that was admissible before the refused firing is refused after it. */
#include "kc.h"

int main(void) {
  kc_theory();
  int OTHER = tc_sort(0);
  int Kc = tc_con((uint16_t)OTHER, 0, 0, NULL);
  SETUP(OTHER > 0 && Kc >= 0);
  kc_ctx_nat(1);
  Term never = kc_u(B1c, kc_num(9));
  Rule r = { .ntell = 1, .tell = { { kc_u(A1c, tc_v(0)), never } }, .make = { kc_u(W1c, tc_v(0)), 2 }, .fresh = -1 };
  int rid = tc_rule(&r);                                 /* tell A1(x) = B1(9): never solvable */
  SETUP(rid >= 0);
  tc_seal();
  Term m1 = tc_meta(), m2 = tc_meta();
  Term k = tc_app(Kc, NULL);
  SETUP(m1 && m2 && k);
  Occ o = tc_fire(rid, NULL, NULL, &m1);                 /* refused: the tell cannot be solved */
  SETUP(o == 0);
  bool t2 = tc_tell(m2, k);                              /* an untouched unknown takes a term of sort OTHER */
  bool t1 = tc_tell(m1, k);                              /* the unknown that only met a refused firing */
  SETUP(t2);
  HOLDS(t1, "an unknown that only appeared in a refused firing accepts the same tell as an untouched one");
  FINISH("k15_refusal_changes_sort");
}
