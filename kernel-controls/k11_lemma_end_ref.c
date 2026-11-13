/* k11: tc_lemma_end(ref) with a step reference that does not exist is refused (-1), not a crash.
   The code reads lsp[ref] before it validates ref. */
#include "kc.h"

static void end_no_steps(void) { if (tc_lemma(0, 0)) (void)tc_lemma_end(0); }
static void end_far(void) { if (tc_lemma(0, 0)) (void)tc_lemma_end(1 << 28); }

int main(void) {
  kc_theory();
  SETUP(tc_ctx(0, NULL));
  int s1 = kc_survives(end_no_steps);
  HOLDS(s1 == 0, "tc_lemma_end(0) with no step checked is refused without a crash");
  if (s1) printf("    child died with signal/status %d\n", s1);
  int s2 = kc_survives(end_far);
  HOLDS(s2 == 0, "tc_lemma_end(2^28) is refused without a crash");
  if (s2) printf("    child died with signal/status %d\n", s2);
  FINISH("k11_lemma_end_ref");
}
