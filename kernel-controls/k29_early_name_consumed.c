/* k29: a name used before it is minted must not let a theory derive what no run derives.
   Theory, all in protected space 1, no absent or count query anywhere:
     initial fact T;
     R1 (pure):  keep T            |- A(x)      (x given by the caller)
     R0:         take T            |- U
     R2:         keep U, fresh n   |- B(n)
     R3:         keep A(x), B(x)   |- W
   In the calculus every name in an A fact exists while T does, and n is minted after T is gone, so W is
   not derivable. A caller who gives R1 the name that R2 will mint next derives W. */
#include "kc.h"

int main(void) {
  kc_theory();
  int Tc = tc_con((uint16_t)THM, 0, 0, NULL), Uc = tc_con((uint16_t)THM, 0, 0, NULL), Wc = tc_con((uint16_t)THM, 0, 0, NULL);
  SETUP(Tc >= 0 && Uc >= 0 && Wc >= 0);
  Term T = tc_app(Tc, NULL), U = tc_app(Uc, NULL), W = tc_app(Wc, NULL);
  kc_ctx_nat(1);
  Term x = tc_v(0);
  Rule r1 = { .nkeep = 1, .keep = { { T, 1 } }, .make = { kc_u(A1c, x), 1 }, .fresh = -1, .inputs = 0x1 };   /* x given by the caller */
  Rule r0 = { .ntake = 1, .take = { { T, 1 } }, .make = { U, 1 }, .fresh = -1 };
  Rule r2 = { .nkeep = 1, .keep = { { U, 1 } }, .make = { kc_u(B1c, x), 1 }, .fresh = 0 };
  Rule r3 = { .nkeep = 2, .keep = { { kc_u(A1c, x), 1 }, { kc_u(B1c, x), 1 } }, .make = { W, 1 }, .fresh = -1 };
  int R1 = tc_rule(&r1), R0 = tc_rule(&r0), R2 = tc_rule(&r2), R3 = tc_rule(&r3);
  SETUP(R1 >= 0 && R0 >= 0 && R2 >= 0 && R3 >= 0);
  Occ ot = tc_post(1, T);
  SETUP(ot);
  tc_protect(1); tc_seal();
  /* untrusted caller from here on */
  Term early = tc_name((uint16_t)NAT, tc_next_name());   /* the name R2 will mint next */
  SETUP(early);
  Occ oa = tc_fire(R1, NULL, &ot, &early);
  HOLDS(oa == 0, "R1 refuses a caller-given name that is not yet minted");
  Occ ou = tc_fire(R0, &ot, NULL, NULL);
  SETUP(ou);
  Occ ob = tc_fire(R2, NULL, &ou, NULL);
  SETUP(ob);
  bool same = tc_term(ob) == kc_u(B1c, early);
  printf("    R2 minted %s\n", same ? "exactly the name R1 was given" : "a name R1 was not given");
  Occ w = 0;
  if (oa) { Occ k[2] = { oa, ob }; w = tc_fire(R3, NULL, k, NULL); }
  HOLDS(w == 0, "W, which no run of the theory derives, is not derived");
  if (w) printf("    W entered protected space 1 (occurrence %u)\n", w);
  FINISH("k29_early_name_consumed");
}
