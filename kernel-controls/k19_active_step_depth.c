/* k19: deep terms are refused, not a crash. tc_active_step recurses with no depth bound. */
#include "kc.h"

static int APPc, LAMc, QUOc, ACTc;
static Term deep;
static void step_deep(void) { (void)tc_active_step(deep); }

int main(void) {
  SETUP(tc_init(1u << 22, 1u << 8));
  NAT = tc_sort(0);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  Binder n2[2] = { { (uint16_t)NAT, 0, 0 }, { (uint16_t)NAT, 0, 0 } };
  Zc = tc_con((uint16_t)NAT, 0, 0, NULL);
  APPc = tc_con((uint16_t)NAT, 0, 2, n2); LAMc = tc_con((uint16_t)NAT, 0, 2, n2);
  QUOc = tc_con((uint16_t)NAT, 0, 1, &n1); ACTc = tc_con((uint16_t)NAT, 0, 1, &n1);
  SETUP(Zc >= 0 && APPc >= 0 && LAMc >= 0 && QUOc >= 0 && ACTc >= 0);
  tc_set_quote_con(QUOc, ACTc, LAMc, APPc);
  Term z = tc_app(Zc, NULL);
  deep = z;
  for (int i = 0; i < 2000000 && deep; i++) deep = tc_app(APPc, (Term[2]){ deep, z });
  SETUP(deep);
  int sig = kc_survives(step_deep);
  HOLDS(sig == 0, "tc_active_step on a 2,000,000-deep application returns without a crash");
  if (sig) printf("    child died with signal/status %d\n", sig);
  FINISH("k19_active_step_depth");
}
