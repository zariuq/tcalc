/* k22: a refused firing leaves the state unchanged, so a later firing is judged as if it never ran.
   A refused firing whose tell meets an unbound hole leaves a sort on the unknown index it used;
   the index is handed out again, and a later, valid firing of another rule is refused, every time.
   Found by the random differential (seed 1999, shrunk to two steps). */
#include "kc.h"

static int NM, MKc;
static int rule_a, rule_b;
static void setup(void) {
  kc_theory();
  NM = tc_sort(0);
  Binder nb[2] = { { (uint16_t)NM, 0, 0 }, { (uint16_t)NAT, 0, 0 } };
  MKc = tc_con((uint16_t)THM, 0, 2, nb);                 /* MK(N, NAT) */
  SETUP(NM > 0 && MKc >= 0);
  (void)tc_fresh_name(); (void)tc_fresh_name(); (void)tc_fresh_name();
  Binder ca[2] = { { (uint16_t)NAT, 0, 0 }, { (uint16_t)NAT, 0, 0 } };
  SETUP(tc_ctx(2, ca));
  Term pairxy = kc_pair(tc_v(0), tc_v(1));
  (void)pairxy;
  Rule a = { .ntell = 1, .tell = { { kc_s(tc_v(0)), kc_z() } }, .make = { kc_u(A1c, tc_v(0)), 0 }, .fresh = -1 };   /* tell S(x) = Z: never solvable */
  rule_a = tc_rule(&a);
  Binder cb[1] = { { (uint16_t)NM, 0, 0 } };
  SETUP(tc_ctx(1, cb));
  Term n2 = tc_name((uint16_t)NM, 2);
  Rule b = { .ntell = 1, .tell = { { tc_v(0), n2 } }, .make = { tc_app(MKc, (Term[2]){ tc_v(0), kc_z() }), 0 }, .fresh = -1 };  /* tell n = n2 |- MK(n, Z) */
  rule_b = tc_rule(&b);
  SETUP(rule_a >= 0 && rule_b >= 0);
  tc_seal();
}

int main(void) {
  setup();
  Occ fresh_kernel = tc_fire(rule_b, NULL, NULL, NULL);
  HOLDS(fresh_kernel != 0, "rule B (tell n = n2 |- MK(n,Z)) fires on a fresh kernel");
  setup();
  Occ refused = tc_fire(rule_a, NULL, NULL, NULL);
  SETUP(refused == 0);
  Occ after = tc_fire(rule_b, NULL, NULL, NULL);
  HOLDS(after != 0, "rule B fires just the same after a refused firing of rule A");
  int tries = 0;
  for (int i = 0; i < 100 && !tc_fire(rule_b, NULL, NULL, NULL); i++) tries++;
  if (!after) printf("    rule B refused %d more times in a row\n", tries);
  FINISH("k22_refusal_poisons_later_firing");
}
