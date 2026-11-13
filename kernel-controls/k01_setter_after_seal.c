/* k01: configuration setters after tc_seal must not change what a sealed store accepts.
   tc_set_rho_con(S, S, false) after sealing makes CV_REFL equate S(S(x)) with x, and
   tc_convert then writes 2 = 0 into the protected space. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule refl = { .make = { kc_eq(tc_v(0), tc_v(0)), 1 }, .fresh = -1, .inputs = 0x1 };   /* x given by the caller */
  int r = tc_rule(&refl);
  SETUP(r >= 0);
  tc_protect(1); tc_seal();
  Term two = kc_num(2), zero = kc_num(0);
  Occ o = tc_fire(r, NULL, NULL, &two);
  SETUP(o && tc_term(o) == kc_eq(two, two));
  Conv rf = { .kind = CV_REFL };
  Term bad = kc_eq(two, zero);
  HOLDS(tc_convert(o, &rf, bad) == 0, "before the setter: |- 2 = 2 does not convert to |- 2 = 0");
  tc_set_rho_con(Sc, Sc, false);                       /* after the seal */
  Occ forged = tc_convert(o, &rf, bad);
  HOLDS(forged == 0, "after tc_set_rho_con(S,S) post-seal: |- 2 = 2 still does not convert to |- 2 = 0");
  if (forged) printf("    forged occurrence %u in protected space 1 states EQ(2,0): %s\n", forged, tc_term(forged) == bad ? "yes" : "no");
  FINISH("k01_setter_after_seal");
}
