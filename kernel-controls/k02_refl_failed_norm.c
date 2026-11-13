/* k02: with a rho pair configured (before the seal, a legitimate theory choice), CV_REFL compares
   tc_rho_norm_name(l) with tc_rho_norm_name(r). Both are 0 when normalization fails (depth past
   4096), and 0 == 0 passes: any two deep terms convert. */
#include "kc.h"

int main(void) {
  SETUP(tc_init(1u << 15, 1u << 8));
  NAT = tc_sort(0); THM = tc_sort(SORT_PROVABLE);
  int NAME = tc_sort(0), PROC = tc_sort(0);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  Binder n2[2] = { { (uint16_t)NAT, 0, 0 }, { (uint16_t)NAT, 0, 0 } };
  Binder pn = { (uint16_t)PROC, 0, 0 }, nn_ = { (uint16_t)NAME, 0, 0 };
  Zc = tc_con((uint16_t)NAT, 0, 0, NULL);
  Sc = tc_con((uint16_t)NAT, 0, 1, &n1);
  EQc = tc_con((uint16_t)THM, 0, 2, n2);
  int QUOTE = tc_con((uint16_t)NAME, 0, 1, &pn), DROP = tc_con((uint16_t)PROC, 0, 1, &nn_);
  SETUP(Zc >= 0 && Sc >= 0 && EQc >= 0 && QUOTE >= 0 && DROP >= 0);
  tc_set_rho_con(QUOTE, DROP, false);                  /* the theory's own rho pair, unrelated to NAT */
  kc_ctx_nat(1);
  Rule refl = { .make = { kc_eq(tc_v(0), tc_v(0)), 1 }, .fresh = -1, .inputs = 0x1 };   /* x given by the caller */
  int r = tc_rule(&refl);
  SETUP(r >= 0);
  tc_protect(1); tc_seal();
  Term big = kc_num(5000), bigger = kc_num(5001), small = kc_num(3);
  SETUP(big && bigger && small);
  Occ o = tc_fire(r, NULL, NULL, &big);
  Occ os = tc_fire(r, NULL, NULL, &small);
  SETUP(o && os);
  Conv rf = { .kind = CV_REFL };
  HOLDS(tc_convert(os, &rf, kc_eq(small, kc_num(4))) == 0, "shallow: |- 3 = 3 does not convert to |- 3 = 4");
  Term bad = kc_eq(big, bigger);
  Occ forged = tc_convert(o, &rf, bad);
  HOLDS(forged == 0, "deep: |- 5000 = 5000 does not convert to |- 5000 = 5001 by reflexivity");
  if (forged) printf("    forged occurrence %u in protected space 1\n", forged);
  FINISH("k02_refl_failed_norm");
}
