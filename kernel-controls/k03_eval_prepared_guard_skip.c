/* k03: a firing whose absent (or count) guard is false must not be committed by any entry point.
   tc_eval_prepared_ex takes the guard switches from its caller and commits with them off. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule neg = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .nabsent = 1, .absent = { { kc_u(B1c, tc_v(0)), 1 } },
               .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };
  Rule cnt = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .ncount = 1, .count = { { kc_u(B1c, tc_v(0)), 1, 2 } },
               .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };
  int rn = tc_rule(&neg), rc = tc_rule(&cnt);
  SETUP(rn >= 0 && rc >= 0);
  Term a = kc_num(1);
  Occ oa = tc_post(1, kc_u(A1c, a)), ob = tc_post(1, kc_u(B1c, a));
  SETUP(oa && ob);
  tc_protect(1); tc_seal();
  HOLDS(tc_fire(rn, NULL, &oa, NULL) == 0, "tc_fire refuses: B1(1) is present, the absent guard is false");
  HOLDS(tc_fire(rc, NULL, &oa, NULL) == 0, "tc_fire refuses: one B1(1), the count guard asks for two");
  TcPreparedStep st = { .rule = rn, .keep = &oa };
  Occ out = 0; uint8_t nm = 0;
  int v = tc_eval_prepared_ex(&st, false, false, false, false, true, NULL, NULL, NULL, &nm, &out);
  HOLDS(!(v == TC_PREP_OK && out), "tc_eval_prepared_ex does not commit the absent-guarded firing with the guard switched off");
  if (out) printf("    committed occurrence %u = W1(1) in protected space 1: %s\n", out, tc_term(out) == kc_u(W1c, a) ? "yes" : "no");
  TcPreparedStep st2 = { .rule = rc, .keep = &oa };
  out = 0;
  v = tc_eval_prepared_ex(&st2, true, false, true, false, true, NULL, NULL, NULL, &nm, &out);
  HOLDS(!(v == TC_PREP_OK && out), "tc_eval_prepared_ex does not commit the count-guarded firing with the count switch off");
  FINISH("k03_eval_prepared_guard_skip");
}
