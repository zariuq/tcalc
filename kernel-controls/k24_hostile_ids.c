/* k24: ids that name nothing are refused, not dereferenced.
   (a) reach seeds are normalized before they are range-checked (tc_reach, tc_fire_reach,
       tc_search_reach, tc_commit_prepared with seeds, tc_eval_prepared_ex with check_reach);
   (b) tc_set_rho_con accepts a "quote" constructor of any arity, and tc_rho_comm then passes a
       one-element array to tc_app (stack over-read; visible under the sanitizer build).
   Found by the random API sequences. */
#include "kc.h"

static int rule0;
static void reach_seed(void) { Term seeds[2] = { 0x0FFFFFF0u, 0xFFFFFFFFu }, out[8]; (void)tc_reach(seeds, 2, out, 8); }
static void fire_seed(void) { Term seeds[1] = { 0x0FFFFFF0u }; Term in = kc_num(1); (void)tc_fire_reach(rule0, NULL, NULL, &in, seeds, 1); }
static void commit_seed(void) {
  Term seeds[1] = { 0x0FFFFFF0u }; Term in = kc_num(1);
  TcPreparedStep st = { .rule = rule0, .inst = &in, .nseeds = 1, .seeds = seeds }; TcAdmissionReceipt rc;
  (void)tc_commit_prepared(&st, &rc);
}
static void rho_arity(void) {
  tc_set_rho_con(EQc, Sc, true);                         /* EQ takes two arguments */
  Term z = kc_z();
  (void)tc_rho_comm(z, z, z, z, 0, 1);
}

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule mk = { .make = { kc_u(A1c, tc_v(0)), 0 }, .fresh = -1 };
  rule0 = tc_rule(&mk);
  SETUP(rule0 >= 0);
  tc_seal();
  int s;
  s = kc_survives(reach_seed);  HOLDS(s == 0, "tc_reach with seeds that are not terms returns without a crash"); if (s) printf("    child died with signal/status %d\n", s);
  s = kc_survives(fire_seed);   HOLDS(s == 0, "tc_fire_reach with such a seed is refused without a crash"); if (s) printf("    child died with signal/status %d\n", s);
  s = kc_survives(commit_seed); HOLDS(s == 0, "tc_commit_prepared with such a seed is refused without a crash"); if (s) printf("    child died with signal/status %d\n", s);
  s = kc_survives(rho_arity);   HOLDS(s == 0, "tc_set_rho_con with a two-argument 'quote' does not make tc_rho_comm read past its argument"); if (s) printf("    child died with signal/status %d (sanitizer build)\n", s);
  FINISH("k24_hostile_ids");
}
