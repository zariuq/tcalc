/* k34: a prepared step with a destination means the same through both commit entry points.
   tc_commit_prepared writes a flat rule's fact at `dest`; tc_eval_prepared_ex(commit) honours `dest`
   only through the ordinary leaf, which declines when hole values are given, and otherwise appends a
   new occurrence. The same step then leaves different stores. Here: rule A1(x)@0 |- B1(x)@0, register
   `dest` holding B1(9) in unprotected space 0, hole value x := 1 given. */
#include "kc.h"

static Occ oa, od; static int rule;
static void scene(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule r = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 0 } }, .make = { kc_u(B1c, tc_v(0)), 0 }, .fresh = -1 };
  rule = tc_rule(&r);
  SETUP(rule >= 0);
  oa = tc_post(0, kc_u(A1c, kc_num(1)));
  od = tc_post(0, kc_u(B1c, kc_num(9)));
  SETUP(oa && od);
  tc_seal();
}
static void describe(char *buf, int cap) {
  int b9 = 0, b1 = 0;
  for (Occ o = 1; o < 64; o++) if (tc_alive(o)) { b9 += tc_term(o) == kc_u(B1c, kc_num(9)); b1 += tc_term(o) == kc_u(B1c, kc_num(1)); }
  snprintf(buf, (size_t)cap, "B1(9) x%d, B1(1) x%d, dest holds %s", b9, b1,
           tc_term(od) == kc_u(B1c, kc_num(1)) ? "B1(1)" : tc_term(od) == kc_u(B1c, kc_num(9)) ? "B1(9)" : "other");
}

int main(void) {
  char a[128], b[128];
  Term one;
  scene(); one = kc_num(1);
  TcPreparedStep s1 = { .rule = rule, .keep = &oa, .inst = &one, .dest = od };
  TcAdmissionReceipt rc;
  SETUP(tc_commit_prepared(&s1, &rc));
  describe(a, sizeof a);
  scene(); one = kc_num(1);
  TcPreparedStep s2 = { .rule = rule, .keep = &oa, .inst = &one, .dest = od };
  Occ out = 0;
  SETUP(tc_eval_prepared_ex(&s2, true, true, true, false, true, NULL, NULL, NULL, NULL, &out) == TC_PREP_OK && out);
  describe(b, sizeof b);
  printf("    tc_commit_prepared:          %s\n    tc_eval_prepared_ex(commit): %s\n", a, b);
  HOLDS(!strcmp(a, b), "both commit entry points leave the same store for the same step");
  FINISH("k34_dest_one_meaning");
}
