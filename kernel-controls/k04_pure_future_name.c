/* k04: a freshly minted name is new to the store wherever a rule can observe it.
   Pure rules skip the check that a caller-given hole value mentions only minted names. A pure rule
   then puts A1(n) on the board for a name n not yet minted; the next fresh firing mints n.
   (a) Theory with an absent query that reads exactly that ("a fresh name has no A1 fact"): the
       collision is observable and the query refuses a firing it must admit.
   (b) Monotone theory (no absent or count): the same collision. A pure fact is schematic, but once a
       theory consumes facts an early-used name can witness what no run derives (k29), so the contract is
       that every name is minted before it is used, in every theory. */
#include "kc.h"

static int part(bool with_query) {
  kc_theory();
  kc_ctx_nat(1);
  Rule mk = { .make = { kc_u(A1c, tc_v(0)), 1 }, .fresh = -1, .inputs = 0x1 };  /* pure: |- A1(x) for given x */
  Rule nw = { .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = 0 };                  /* B1(n) for a fresh n */
  Rule ok = { .nkeep = 1, .keep = { { kc_u(B1c, tc_v(0)), 1 } }, .nabsent = 1, .absent = { { kc_u(A1c, tc_v(0)), 1 } },
              .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };                 /* B1(n), absent A1(n) |- W1(n): n is unused */
  int rmk = tc_rule(&mk), rnw = tc_rule(&nw), rok = with_query ? tc_rule(&ok) : -1;
  SETUP(rmk >= 0 && rnw >= 0 && (!with_query || rok >= 0));
  tc_protect(1); tc_seal();
  uint64_t next = tc_next_name();
  Term future = tc_name((uint16_t)NAT, next);
  SETUP(future);
  if (with_query) HOLDS(tc_post(2, kc_u(A1c, future)) == 0, "tc_post refuses a term over a name not yet minted");
  Occ o = tc_fire(rmk, NULL, NULL, &future);
  Occ f = tc_fire(rnw, NULL, NULL, NULL);
  SETUP(f);
  bool collide = o && tc_term(f) == kc_u(B1c, future);
  if (!with_query) {
    HOLDS(o == 0, "(b) in a monotone theory too, a pure rule refuses a hole value over a name not yet minted");
    HOLDS(!collide, "(b) the freshly minted name does not already occur in the store");
    return 0;
  }
  HOLDS(o == 0, "(a) with an absent query in the theory, a pure rule refuses a hole value over a name not yet minted");
  Occ w = tc_fire(rok, NULL, &f, NULL);
  HOLDS(w != 0, "(a) the freshly minted name has no A1 fact, so B1(n), absent A1(n) |- W1(n) fires");
  if (!w) printf("    A1(n%llu) was put on the board before n%llu was minted\n", (unsigned long long)next, (unsigned long long)next);
  return 0;
}

int main(void) {
  part(true);
  part(false);
  FINISH("k04_pure_future_name");
}
