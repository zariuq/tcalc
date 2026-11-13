/* k06: an occurrence in a sealed protected space keeps its content.
   tc_term(o) on a flat-made occurrence inside a tc_transient scope stores a transient node id in
   the board; installing any lemma releases the node; the next term made reuses the id, and the
   general firing path then reads the occurrence as that other term. Every call is made after the seal. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(2);
  Rule join = { .nkeep = 2, .keep = { { kc_u(A1c, tc_v(0)), 1 }, { kc_u(B1c, tc_v(1)), 1 } },
                .make = { kc_pair(tc_v(0), tc_v(1)), 1 }, .fresh = -1 };            /* flat: A1(x), B1(y) |- PAIR(x,y) */
  Rule win = { .nkeep = 1, .keep = { { kc_eq(tc_v(0), tc_v(1)), 1 } },
               .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };                     /* EQ(x,y) |- W1(x) */
  int rj = tc_rule(&join), rw = tc_rule(&win);
  SETUP(rj >= 0 && rw >= 0);
  Term a = kc_num(1), b = kc_num(2);
  Term fa = kc_u(A1c, a), fb = kc_u(B1c, b);
  Occ oa = tc_post(1, fa), ob = tc_post(1, fb);
  SETUP(oa && ob);
  tc_protect(1); tc_seal();
  SETUP(tc_ctx(0, NULL));
  Occ keep[2] = { oa, ob };
  Occ o = tc_flat_fire(rj, keep, NULL, 0);               /* a legitimate firing: PAIR(1,2) */
  SETUP(o);
  tc_transient();
  Term seen = tc_term(o);                                /* materializes PAIR(1,2) inside the scope */
  SETUP(seen);
  SETUP(tc_lemma(0, 1) && tc_lemma_hyp(fa));
  int lem = tc_lemma_end(-1);                            /* A1(1) |- A1(1): trivially sound, releases the scope */
  SETUP(lem >= 0);
  Term other = kc_eq(a, b);                              /* a term that was never derived */
  SETUP(other);
  Term now = tc_term(o);
  HOLDS(now != other, "the occurrence does not read as a term that was never derived");
  const Term *row = tc_flat_args(o, ((uint32_t)PAIRc << 9) | (1u << 1) | 1u);
  printf("    tc_term(o) is %s; its flat row is %s PAIR(1,2)\n", now == other ? "EQ(1,2)" : "not EQ(1,2)",
         row && row[0] == a && row[1] == b ? "still" : "not");
  Term none[2] = { 0, 0 };
  Occ w = tc_fire(rw, NULL, &o, none);                   /* general path: reads tc_term(o) */
  HOLDS(w == 0, "EQ(x,y) |- W1(x) does not fire on an occurrence whose fact is PAIR(1,2)");
  if (w) printf("    W1(1) is now in protected space 1 (occurrence %u), derived from EQ(1,2), which no rule made\n", w);
  FINISH("k06_transient_term_release");
}
