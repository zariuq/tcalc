/* k05: a sealed protected space changes only by firings.
   tc_unset(u) after the seal turns every free board slot into a live copy of u, so a
   single linear token can be taken many times. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule spend = { .ntake = 1, .take = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(W1c, tc_v(0)), 2 }, .fresh = -1 };
  int r = tc_rule(&spend);
  SETUP(r >= 0);
  Term a = kc_num(1);
  Occ coin = tc_post(1, kc_u(A1c, a));
  SETUP(coin);
  tc_protect(1); tc_seal();
  int alive_before = 0;
  for (Occ o = 1; o < 4096; o++) alive_before += tc_alive(o) && tc_term(o) == kc_u(A1c, a);
  tc_unset(coin);                                        /* after the seal */
  int alive_after = 0;
  for (Occ o = 1; o < 4096; o++) alive_after += tc_alive(o) && tc_term(o) == kc_u(A1c, a);
  HOLDS(alive_after == alive_before, "tc_unset after the seal leaves the number of live A1(1) occurrences unchanged");
  printf("    live copies of the token: %d before, %d after\n", alive_before, alive_after);
  int spent = 0;
  for (Occ o = 1; o < 64 && spent < 8; o++) if (tc_alive(o)) { Occ t = o; if (tc_fire(r, &t, NULL, NULL)) spent++; }
  HOLDS(spent <= 1, "the single token is spent at most once");
  printf("    spend firings admitted: %d\n", spent);
  FINISH("k05_unset_after_seal");
}
