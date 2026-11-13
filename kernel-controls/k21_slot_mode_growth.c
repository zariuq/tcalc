/* k21: the board grows with what is stored, not with the number of posts.
   In slot mode (after tc_unset) post() sets nw = wcap after every write, so the next post finds the
   board full and doubles it: n posts cost 2^n slots. Twelve posts reach a million slots; about
   nineteen more hit the 2^27 cap (several GiB). Slot mode is a fixed register table, so the bound to
   hold is: no post makes the board grow past its register slots. */
#include "kc.h"

int main(void) {
  kc_theory();
  Occ u = tc_post(0, kc_u(A1c, kc_num(0)));
  SETUP(u);
  tc_unset(u);
  Occ maxo = 0; int accepted = 0;
  for (int i = 1; i <= 12; i++) {
    Occ o = tc_post(0, kc_u(B1c, kc_num(i)));
    if (o) { accepted++; if (o > maxo) maxo = o; }
  }
  printf("    posts accepted after tc_unset: %d; largest occurrence id: %u\n", accepted, maxo);
  HOLDS(maxo < 4096, "twelve posts into a 256-slot register board use fewer than 4096 occurrence ids");
  Occ k[1] = { u };
  (void)k;
  FINISH("k21_slot_mode_growth");
}
