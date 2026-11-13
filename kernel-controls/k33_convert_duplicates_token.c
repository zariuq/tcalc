/* k33: a conversion rewrites a fact; it does not copy a resource.
   tc_convert posts the converted term next to the source occurrence and keeps the source. In a theory
   that consumes facts (take), that makes two tokens from one: with plain reflexivity (the target is
   the source's own term) a caller doubles a linear token in a protected space after the seal and
   spends it twice. tc_active_step_occ and tc_rho_step_occ post their results the same way. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule spend = { .ntake = 1, .take = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(W1c, tc_v(0)), 2 }, .fresh = -1 };
  int r = tc_rule(&spend);
  SETUP(r >= 0);
  Term coin = kc_u(A1c, kc_num(1));
  Occ oc = tc_post(1, coin);
  SETUP(oc);
  tc_protect(1); tc_protect(2); tc_seal();
  Conv refl = { .kind = CV_REFL };
  Occ copy = tc_convert(oc, &refl, coin);
  int live = 0;
  for (Occ o = 1; o < 64; o++) live += tc_alive(o) && tc_term(o) == coin;
  HOLDS(live <= 1, "after a conversion there is still one live token A1(1)");
  printf("    conversion %s; live tokens: %d\n", copy ? "admitted" : "refused", live);
  int spent = 0;
  for (Occ o = 1; o < 64; o++) if (tc_alive(o) && tc_term(o) == coin) { Occ t = o; if (tc_fire(r, &t, NULL, NULL)) spent++; }
  HOLDS(spent <= 1, "the token is spent at most once");
  printf("    spend firings admitted: %d\n", spent);
  FINISH("k33_convert_duplicates_token");
}
