/* k14: a receipt lists exactly the occurrences its firing made.
   last_extra_occ is reset only on the general path; a later flat firing's receipt (and
   tc_last_extra) still lists the extra occurrences of an earlier, different firing. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule two = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(B1c, tc_v(0)), 1 },
               .nmake_extra = 1, .make_extra = { { kc_u(W1c, tc_v(0)), 1 } }, .fresh = -1 };   /* A1(x) |- B1(x), W1(x) */
  Rule one = { .nkeep = 1, .keep = { { kc_u(B1c, tc_v(0)), 1 } }, .make = { kc_eq(tc_v(0), tc_v(0)), 1 }, .fresh = -1 }; /* B1(x) |- EQ(x,x), flat */
  int r2 = tc_rule(&two), r1 = tc_rule(&one);
  SETUP(r2 >= 0 && r1 >= 0);
  Occ oa = tc_post(1, kc_u(A1c, kc_num(1)));
  SETUP(oa);
  tc_protect(1); tc_seal();
  TcAdmissionReceipt rc2, rc1;
  TcPreparedStep s2 = { .rule = r2, .keep = &oa };
  SETUP(tc_commit_prepared(&s2, &rc2) && rc2.nextra == 1 && rc2.extra[0]);
  Occ ob = rc2.out;
  TcPreparedStep s1 = { .rule = r1, .keep = &ob };
  SETUP(tc_commit_prepared(&s1, &rc1));
  HOLDS(rc1.nextra == 0, "the receipt of a one-make firing lists no extra occurrences");
  if (rc1.nextra) printf("    receipt of rule %d lists extra occurrence %u, which rule %d made earlier\n", r1, rc1.extra[0], r2);
  HOLDS(tc_last_extra(0) == 0, "tc_last_extra(0) is 0 after a one-make firing");
  FINISH("k14_receipt_stale_extra");
}
