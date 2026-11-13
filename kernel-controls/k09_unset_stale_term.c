/* k09: the flat path and the general path read the same fact from one occurrence.
   tc_unset (before the seal, as the slot-mode checkers use it) clears wt_dirty although other
   occurrences keep a materialized term in Wt. An in-place flat write to such an occurrence (here in
   unprotected space 0, the register use of slot mode) then leaves Wt holding the old term while the
   row holds the new one: the general path (tc_term, tc_fire with hole values) reads one fact and the
   flat path (tc_flat_fire) reads another, and a rule that copies into protected space 1 makes
   different facts depending on the entry point. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule ab = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 0 } }, .make = { kc_u(B1c, tc_v(0)), 0 }, .fresh = -1 };   /* A1(x)@0 |- B1(x)@0 */
  Rule bw = { .nkeep = 1, .keep = { { kc_u(B1c, tc_v(0)), 0 } }, .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };   /* B1(x)@0 |- W1(x)@1 */
  int rab = tc_rule(&ab), rbw = tc_rule(&bw);
  SETUP(rab >= 0 && rbw >= 0);
  Term one = kc_num(1), two = kc_num(2);
  Occ oa = tc_post(0, kc_u(A1c, one)), ob = tc_post(0, kc_u(B1c, two)), ou = tc_post(0, kc_u(A1c, kc_num(5)));
  SETUP(oa && ob && ou);
  tc_unset(ou);                                          /* slot mode, before the seal */
  tc_protect(1); tc_seal();
  Occ k1[1] = { oa };
  Occ o = tc_flat_fire(rab, k1, NULL, ob);               /* register write into ob, unprotected space 0 */
  SETUP(o == ob);
  const Term *row = tc_flat_args(ob, ((uint32_t)B1c << 9) | (0u << 1) | 1u);
  SETUP(row && row[0] == one);                           /* the row now says B1(1) */
  HOLDS(tc_term(ob) == kc_u(B1c, one), "tc_term reads the fact the row holds (B1(1))");
  Occ kb[1] = { ob };
  Term none[1] = { 0 };
  Occ g = tc_fire(rbw, NULL, kb, none);                  /* general path */
  Occ f = tc_flat_fire(rbw, kb, NULL, 0);                /* flat path */
  SETUP(g && f);
  HOLDS(tc_term(g) == tc_term(f), "the general and the flat firing of B1(x)@0 |- W1(x)@1 on the same occurrence make the same fact");
  printf("    general path made W1(%s), flat path made W1(%s), both in protected space 1\n",
         tc_term(g) == kc_u(W1c, one) ? "1" : tc_term(g) == kc_u(W1c, two) ? "2" : "?",
         tc_term(f) == kc_u(W1c, one) ? "1" : tc_term(f) == kc_u(W1c, two) ? "2" : "?");
  FINISH("k09_unset_stale_term");
}
