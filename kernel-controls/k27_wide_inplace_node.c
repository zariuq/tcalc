/* k27: a write to one occurrence changes no other occurrence, and a term node never changes.
   post() records a wide fact (arity > 4) by pointing Warg at the term node's own argument array.
   An in-place flat write (tc_flat_fire with a destination) into such an occurrence writes through
   that pointer: it rewrites the hash-consed node itself. Every other fact holding the same term,
   in any space, protected or not, now reads the new arguments, and the node no longer matches its
   hash slot. Here the caller writes only into unprotected space 0, after the seal; the fact in
   protected space 1 changes. */
#include "kc.h"

int main(void) {
  kc_theory();
  Binder w5[5];
  for (int i = 0; i < 5; i++) w5[i] = (Binder){ (uint16_t)NAT, 0, 0 };
  int W5 = tc_con((uint16_t)THM, 0, 5, w5);
  SETUP(W5 >= 0);
  kc_ctx_nat(1);
  Term x = tc_v(0);
  Term five_x[5] = { x, x, x, x, x };
  Rule spread = { .nkeep = 1, .keep = { { kc_u(A1c, x), 0 } }, .make = { tc_app(W5, five_x), 0 }, .fresh = -1 };  /* A1(x)@0 |- W5(x,x,x,x,x)@0 */
  int r = tc_rule(&spread);
  SETUP(r >= 0);
  Term one = kc_num(1), two = kc_num(2);
  Term ones[5] = { one, one, one, one, one }, twos[5] = { two, two, two, two, two };
  Term w_one = tc_app(W5, ones);
  SETUP(w_one);
  Occ prot = tc_post(1, w_one);                          /* the theory's fact W5(1,1,1,1,1) in protected space 1 */
  SETUP(prot);
  tc_protect(1); tc_seal();
  /* untrusted caller: writes only into unprotected space 0 */
  Occ scratch = tc_post(0, w_one);
  Occ oa = tc_post(0, kc_u(A1c, two));
  SETUP(scratch && oa);
  Occ o = tc_flat_fire(r, &oa, NULL, scratch);           /* in place into the space-0 occurrence */
  SETUP(o);
  uint8_t kind; uint32_t head; int ar; const Term *args;
  tc_node(tc_term(prot), &kind, &head, &ar, &args);
  SETUP(kind == K_APP && (int)head == W5 && ar == 5);
  HOLDS(args[0] == one && args[4] == one, "the fact in protected space 1 still reads W5(1,1,1,1,1)");
  tc_node(w_one, &kind, &head, &ar, &args);
  HOLDS(args[0] == one, "the hash-consed node for W5(1,1,1,1,1) still has the arguments it was made with");
  Term w_two = tc_app(W5, twos);
  HOLDS(w_two != w_one || args[0] == one, "W5(2,2,2,2,2) and W5(1,1,1,1,1) are not the same node");
  HOLDS(tc_app(W5, ones) == w_one, "making W5(1,1,1,1,1) again returns the original node");
  FINISH("k27_wide_inplace_node");
}
