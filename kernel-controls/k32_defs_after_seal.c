/* k32: what stays open after the seal (tc_sort, tc_con, tc_def: the HOL checker declares type
   constructors while it replays) cannot touch what is sealed.
   After the seal the control declares sorts, constructors and definitions, including a definition
   whose body uses the sealed constructors, and checks that
   - every sort, constructor and rule that existed at the seal reads back unchanged (sort flags,
     constructor sort, arity, binder shape, argument sorts, definition flag; the stored rule);
   - a new definition is a new constructor id, and no unfolding can be attached to a sealed one
     (CV_UNFOLD on a sealed, non-defined constructor is refused);
   - the sealed rules still fire as before on the protected store. */
#include "kc.h"
#include "tisa/tc_theory_inspect.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule ab = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = -1 };
  int rab = tc_rule(&ab);
  SETUP(rab >= 0);
  Occ oa = tc_post(1, kc_u(A1c, kc_num(1)));
  SETUP(oa);
  tc_protect(1); tc_seal();
  int ns = tc_inspect_sort_count(), nc = tc_inspect_con_count(), nr = tc_rule_count();
  uint8_t sflags[64]; TcInspectCon cons[64]; TcInspectRule rules[4];
  SETUP(ns < 64 && nc < 64 && nr <= 4);
  for (int s = 0; s < ns; s++) sflags[s] = tc_inspect_sort_flags(s);
  for (int c = 0; c < nc; c++) SETUP(tc_inspect_con(c, &cons[c]));
  for (int r = 0; r < nr; r++) SETUP(tc_inspect_rule(r, &rules[r], NULL));
  /* after the seal: new sorts, constructors and definitions */
  int s2 = tc_sort(SORT_PROVABLE), s3 = tc_sort(0);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  int c2 = tc_con((uint16_t)NAT, 0, 1, &n1);
  kc_ctx_nat(1);
  int d1 = tc_def((uint16_t)THM, 0, 1, 0, kc_u(B1c, kc_s(tc_v(0))));   /* D(x) := B1(S(x)) */
  SETUP(tc_ctx(0, NULL));
  int d2 = tc_def((uint16_t)NAT, 0, 0, 0, kc_num(2));                   /* TWO := S(S(Z)) */
  printf("    after the seal: sorts %d, %d; constructor %d; definitions %d, %d\n", s2, s3, c2, d1, d2);
  bool same = tc_inspect_sort_count() >= ns && tc_inspect_con_count() >= nc && tc_rule_count() == nr;
  for (int s = 0; s < ns; s++) same &= tc_inspect_sort_flags(s) == sflags[s];
  for (int c = 0; c < nc; c++) { TcInspectCon now; same &= tc_inspect_con(c, &now) && !memcmp(&now, &cons[c], sizeof now); }
  for (int r = 0; r < nr; r++) { TcInspectRule now; same &= tc_inspect_rule(r, &now, NULL) && !memcmp(&now.decl_rule, &rules[r].decl_rule, sizeof now.decl_rule) && now.nvars == rules[r].nvars; }
  HOLDS(same, "every sort, constructor and rule that existed at the seal reads back unchanged");
  HOLDS((d1 < 0 || d1 >= nc) && (d2 < 0 || d2 >= nc) && (c2 < 0 || c2 >= nc), "new constructors and definitions get new ids");
  Term one = kc_num(1);
  Conv unf = { .kind = CV_UNFOLD, .con = A1c, .kid = &(Conv){ .kind = CV_REFL } };
  HOLDS(tc_convert(oa, &unf, kc_u(B1c, one)) == 0, "no unfolding can be attached to the sealed constructor A1");
  Occ ob = tc_fire(rab, NULL, &oa, NULL);
  HOLDS(ob && tc_term(ob) == kc_u(B1c, one), "the sealed rule still makes B1(1) from A1(1)");
  FINISH("k32_defs_after_seal");
}
