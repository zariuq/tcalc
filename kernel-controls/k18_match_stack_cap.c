/* k18: a fixed cap is reported, not turned into a refusal that looks like a mismatch.
   The bytecode matcher's stack holds 512 terms; a premise pattern of arity-32 constructors nested
   17 deep needs more, and the firing is refused although the fact matches the pattern. */
#include "kc.h"

int main(void) {
  kc_theory();
  Binder w[32];
  for (int i = 0; i < 32; i++) w[i] = (Binder){ (uint16_t)NAT, 0, 0 };
  int WIDE = tc_con((uint16_t)NAT, 0, 32, w);
  SETUP(WIDE >= 0);
  kc_ctx_nat(1);
  Term z = kc_z();
  for (int depth = 2; depth <= 20; depth += 3) {
    Term pat = tc_v(0), fact = kc_num(1);
    for (int d = 0; d < depth; d++) {
      Term pa[32], fa[32];
      pa[0] = kc_s(pat); fa[0] = kc_s(fact);             /* S(.) keeps each level non-flat */
      for (int i = 1; i < 32; i++) pa[i] = fa[i] = z;
      pat = tc_app(WIDE, pa); fact = tc_app(WIDE, fa);
      SETUP(pat && fact);
    }
    Rule r = { .nkeep = 1, .keep = { { kc_u(A1c, pat), 0 } }, .make = { kc_u(W1c, tc_v(0)), 0 }, .fresh = -1 };
    int rid = tc_rule(&r);
    SETUP(rid >= 0);
    Occ o = tc_post(0, kc_u(A1c, fact));
    SETUP(o);
    Occ got = tc_fire(rid, NULL, &o, NULL);
    char what[96];
    snprintf(what, sizeof what, "a matching fact fires at pattern depth %d (arity 32)", depth);
    HOLDS(got && tc_term(got) == kc_u(W1c, kc_num(1)), what);
  }
  FINISH("k18_match_stack_cap");
}
