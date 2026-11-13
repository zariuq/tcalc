/* k30: names are minted before use, on every entry point, and a minted name is then accepted.
   (Control written by Codex, main:5, for the same defect as k04; kept for the paths k04 lacks.)
   The prepared commit path refuses a pure rule's hole value over a name not yet minted and issues no
   receipt; after a fresh firing mints that name, the same candidate is admitted with a receipt naming
   the made term, and the ordinary and flat entry points accept it too. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule make = { .make = { kc_u(A1c, tc_v(0)), 1 }, .fresh = -1, .inputs = 0x1 };   /* x given by the caller */
  Rule fresh = { .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = 0 };
  int make_rule = tc_rule(&make), fresh_rule = tc_rule(&fresh);
  SETUP(make_rule >= 0 && fresh_rule >= 0);
  tc_protect(1);
  tc_seal();
  Term candidate = tc_name((uint16_t)NAT, tc_next_name());
  SETUP(candidate);
  TcPreparedStep step = { .rule = make_rule, .inst = &candidate };
  TcAdmissionReceipt receipt = {0};
  HOLDS(!tc_commit_prepared(&step, &receipt), "prepared commit refuses an unminted name in a pure rule");
  HOLDS(!receipt.admitted && receipt.out == 0, "refusal supplies no admission receipt");
  SETUP(tc_fire(fresh_rule, NULL, NULL, NULL));
  HOLDS(tc_commit_prepared(&step, &receipt), "the same prepared term is admitted after its name is minted");
  HOLDS(receipt.admitted && receipt.out && tc_term(receipt.out) == kc_u(A1c, candidate),
        "the post-mint receipt names the actual made term");
  HOLDS(tc_fire(make_rule, NULL, NULL, &candidate) != 0, "ordinary firing accepts a minted name");
  HOLDS(tc_flat_fire(make_rule, NULL, &candidate, 0) != 0, "flat firing accepts a minted name");
  FINISH("k30_prepared_and_minted");
}
