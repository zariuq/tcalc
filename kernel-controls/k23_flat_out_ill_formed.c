/* k23: every fact in a protected space is a well-formed term.
   tc_flat_out writes a row without checking its arguments. In an unprotected space that row can be
   ill-sorted or hold a rule hole; a flat rule that reads the unprotected space and makes into a
   protected one copies the argument, with no check, into the protected store.
   Second part: an id that is no term at all makes the kernel read outside its node array. */
#include "kc.h"

static int rcopy; static Occ slot;
static void wild(void) {
  Term bad = 0x0FFFFFF0u;
  (void)tc_flat_out(0, 0, A1c, &bad);
  Occ o2 = tc_flat_out(slot, 0, A1c, &bad);
  if (o2) (void)tc_fire(rcopy, NULL, &o2, NULL);
}

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule copy = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 0 } }, .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = -1 };   /* A1(x)@0 |- B1(x)@1 */
  rcopy = tc_rule(&copy);
  SETUP(rcopy >= 0);
  Term hole = tc_v(0);
  slot = tc_post(0, kc_u(A1c, kc_num(1)));
  SETUP(slot);
  tc_protect(1); tc_seal();
  Term thm = kc_eq(kc_z(), kc_z());                       /* sort THM: not a NAT */
  SETUP(tc_app(A1c, &thm) == 0 && tc_post(0, hole) == 0);
  Occ o = tc_flat_out(slot, 0, A1c, &thm);
  HOLDS(o == 0, "tc_flat_out refuses an argument of the wrong sort");
  Occ made = o ? tc_fire(rcopy, NULL, &o, NULL) : 0;
  bool ill = false;
  if (made) {
    uint8_t kind; uint32_t head; int ar; const Term *args;
    tc_node(tc_term(made), &kind, &head, &ar, &args);
    ill = (int)head == B1c && ar == 1 && tc_sort_of(args[0]) != (uint16_t)NAT;
  }
  HOLDS(!ill, "no fact B1(t) with t not a NAT enters protected space 1");
  if (ill) printf("    occurrence %u in protected space 1 is B1(EQ(Z,Z)); tc_app refuses to form that term\n", made);
  Occ oh = tc_flat_out(slot, 0, A1c, &hole);
  HOLDS(oh == 0, "tc_flat_out refuses a rule hole as an argument");
  int sig = kc_survives(wild);
  HOLDS(sig == 0, "tc_flat_out with an id that is no term does not crash the kernel");
  if (sig) printf("    child died with signal/status %d\n", sig);
  FINISH("k23_flat_out_ill_formed");
}
