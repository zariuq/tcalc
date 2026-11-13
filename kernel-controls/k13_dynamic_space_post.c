/* k13: after the seal, only a firing bears a space.
   Protection is a flag per static space (0..255); a dynamic space (any other name of the space sort)
   cannot be protected. After the seal a caller can post a birth marker into a dynamic space with
   tc_post_at, and the birth law then sees the space as born although no firing bore it.
   Posting ordinary facts into dynamic spaces after the seal is allowed by design (the reach tests of
   the Megalodon checker do it); that is reported, not judged. */
#include "kc.h"

int main(void) {
  kc_theory();
  uint16_t SP = tc_space_sort();
  SETUP(SP);
  for (int s = 0; s < 256; s++) tc_protect((uint8_t)s);  /* protect every static space */
  for (int i = 0; i < 6; i++) (void)tc_fresh_name();
  Term dyn = tc_name(SP, 5);                             /* a dynamic space name (minted) */
  SETUP(dyn);
  tc_seal();
  Term a = kc_u(A1c, kc_num(1));
  HOLDS(tc_post_at(tc_space_term(1), a, false) == 0, "tc_post_at into protected static space 1 is refused after the seal");
  HOLDS(tc_space_born(dyn) == false, "the dynamic space is not born before anything happens");
  Occ m = tc_post_at(dyn, a, true);
  HOLDS(m == 0, "tc_post_at cannot post a birth marker after the seal");
  HOLDS(tc_space_born(dyn) == false, "no firing bore the dynamic space, so it is not born");
  Occ f = tc_post_at(dyn, a, false);
  printf("    (by design) a fact posted into the dynamic space after the seal: %s\n", f ? "accepted" : "refused");
  FINISH("k13_dynamic_space_post");
}
