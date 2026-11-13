/* k12: reach. A firing under tc_fire_reach writes only into spaces reachable from the seeds.
   static_space_of() decodes a static space from the low 8 bits of a reserved name id without
   checking the other bits, so the name (1<<62)|0x100|1 is a second handle for static space 1.
   Reach compares handle terms; the made fact lands in space 1 although its handle was not reachable. */
#include "kc.h"

int main(void) {
  kc_theory();
  uint16_t SP = tc_space_sort();
  SETUP(SP);
  Binder ctx[2] = { { SP, 0, 0 }, { (uint16_t)NAT, 0, 0 } };
  SETUP(tc_ctx(2, ctx));
  Term pat = tc_at_space(tc_v(0), kc_u(W1c, tc_v(1)));
  SETUP(pat);
  Rule put = { .make = { pat, 0 }, .fresh = -1 };        /* make W1(x) at the space named by hole 0 */
  int r = tc_rule(&put);
  SETUP(r >= 0);
  tc_protect(1); tc_seal();
  Term a = kc_num(1);
  Term sp1 = tc_space_term(1), sp2 = tc_space_term(2);
  Term alias = tc_name(SP, (1ull << 62) | 0x100u | 1u);
  SETUP(sp1 && sp2 && alias && alias != sp1);
  Term in_direct[2] = { sp1, a };
  HOLDS(tc_fire_reach(r, NULL, NULL, in_direct, &sp2, 1) == 0, "holding only space 2, a make at space 1 is refused");
  Term in_alias[2] = { alias, a };
  Occ o = tc_fire_reach(r, NULL, NULL, in_alias, &alias, 1);
  bool landed = o && tc_occ_space(o) == sp1;
  HOLDS(!landed, "holding only an alias name, a make does not land in static space 1");
  if (landed) printf("    occurrence %u = W1(1) is in static space 1 (protected); the seeds held only the alias\n", o);
  FINISH("k12_static_space_alias");
}
