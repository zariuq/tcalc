/* k26: absent reads the store, whatever scope the fact was made in.
   A firing made inside a tc_birth scope builds its result with mk() while hash-consing is off, so
   the board holds a second node for a term that already has a canonical node. The absent check's
   shortcut (`!Nocc[p]`, keyed by the canonical id) then reports the fact absent although it is live.
   Every call below is made after the seal, through the public API only. */
#include "kc.h"

int main(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule ab = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = -1 };   /* A1(x) |- B1(x) */
  Rule neg = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .nabsent = 1, .absent = { { kc_u(B1c, tc_v(0)), 1 } },
               .make = { kc_u(W1c, tc_v(0)), 1 }, .fresh = -1 };                                                      /* A1(x), absent B1(x) |- W1(x) */
  int rab = tc_rule(&ab), rneg = tc_rule(&neg);
  SETUP(rab >= 0 && rneg >= 0);
  Term one = kc_num(1);
  Term b1 = kc_u(B1c, one);                              /* canonical B1(1), made before the seal */
  Occ oa = tc_post(1, kc_u(A1c, one));
  SETUP(oa && b1);
  tc_protect(1); tc_seal();
  /* untrusted caller from here on */
  tc_birth();
  Occ ob = tc_fire(rab, NULL, &oa, NULL);                /* a legitimate firing: B1(1) into space 1 */
  SETUP(ob);
  uint8_t kind; uint32_t head; int ar; const Term *args;
  tc_node(tc_term(ob), &kind, &head, &ar, &args);
  SETUP(kind == K_APP && (int)head == B1c && ar == 1 && args[0] == one);
  HOLDS(tc_term(ob) == b1, "the made fact B1(1) is the canonical node for B1(1) (hash-consed identity)");
  Occ w = tc_fire(rneg, NULL, &oa, NULL);
  HOLDS(w == 0, "absent B1(1) is false while B1(1) is live in space 1");
  if (w) printf("    W1(1) entered protected space 1 (occurrence %u) although B1(1) is live (occurrence %u)\n", w, ob);
  FINISH("k26_birth_scope_duplicate_absent");
}
