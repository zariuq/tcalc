/* k10: located-pattern nodes (tc_at_space / tc_at_birth) are pattern syntax, not terms.
   tc_post accepts one as a fact and tc_app accepts one as a constructor argument (its sort is the
   inner term's); the board tag is then computed from head 0xFFFFFFFE and the constructor table is
   indexed far out of bounds (tc_unset, emit, fv). */
#include "kc.h"

static Term at_fact;
static Occ at_occ;
static void crash_unset(void) { tc_unset(at_occ); }
static void crash_emit(void) {
  kc_ctx_nat(1);
  Term sp = tc_space_term(3);
  Term nested = kc_u(A1c, tc_at_space(sp, tc_v(0)));
  if (!nested) return;
  Rule r = { .nkeep = 1, .keep = { { nested, 0 } }, .make = { kc_u(W1c, tc_v(0)), 0 }, .fresh = -1 };
  int id = tc_rule(&r);
  if (id >= 0) (void)tc_rule_fibre(id);                  /* compiles the pattern */
}

int main(void) {
  kc_theory();
  Term sp = tc_space_term(3);
  Term a = kc_num(1);
  at_fact = tc_at_space(sp, kc_u(A1c, a));
  SETUP(sp && at_fact);
  at_occ = tc_post(0, at_fact);
  HOLDS(at_occ == 0, "tc_post refuses a located-pattern node as a fact");
  Term smuggled = kc_u(A1c, tc_at_space(sp, a));
  HOLDS(smuggled == 0, "tc_app refuses a located-pattern node as a constructor argument");
  if (at_occ) {
    int sig = kc_survives(crash_unset);
    HOLDS(sig == 0, "tc_unset on that occurrence does not crash");
    if (sig) printf("    child died with signal/status %d\n", sig);
  }
  int sig2 = kc_survives(crash_emit);
  HOLDS(sig2 == 0, "installing a rule whose pattern nests a located node does not crash");
  if (sig2) printf("    child died with signal/status %d\n", sig2);
  FINISH("k10_at_node_as_term");
}
