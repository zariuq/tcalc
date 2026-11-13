/* k17: a rule installed in a tc_birth scope means what was checked.
   Its bytecode is compiled before the scope's nodes are released, but the stored patterns
   (RULE(k)->keep[i].t, k->make) keep the released ids. Two later readers use them:
   (a) prep_flat, on the first tc_fire or at tc_seal, builds the flat layout from whatever terms
       now have those ids. Every call below is made after the seal; the lemma checked is
       A1(x) |- B1(x), the rule that fires is A1(x) |- W1(x).
   (b) when a pattern is larger than the 4096-word bytecode budget (or the 2^20-word code arena is
       full) the rule has no bytecode, and tc_lemma_step falls back to matching the stored patterns:
       a later statement's own terms stand in for the cited rule's hypotheses and conclusion. */
#include "kc.h"

static int part_a(void) {
  kc_theory();
  kc_ctx_nat(1);
  Rule ab = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(B1c, tc_v(0)), 1 }, .fresh = -1 };   /* A1(x) |- B1(x) */
  int rab = tc_rule(&ab);
  SETUP(rab >= 0);
  Term one = kc_num(1);
  Occ oa = tc_post(1, kc_u(A1c, one));
  SETUP(oa);
  tc_protect(1); tc_seal();
  /* from here on: an untrusted caller */
  kc_ctx_nat(1);
  Term x = tc_v(0);
  tc_birth();
  Term hyp = tc_app(A1c, &x);
  SETUP(hyp && tc_lemma(1, 1) && tc_lemma_hyp(hyp));
  Step st = { .kind = ST_RULE, .rule = rab, .prem = { -1 } };
  int s0 = tc_lemma_step(&st);
  SETUP(s0 == 0);
  int lem = tc_lemma_end(s0);                            /* installs A1(x) |- B1(x), releases the scope */
  SETUP(lem >= 0);
  tc_birth();                                            /* fresh nodes take the two released ids */
  Term again = tc_app(A1c, &x), forged = tc_app(W1c, &x);
  SETUP(again == hyp && forged == hyp + 1);
  Occ w = tc_fire(lem, NULL, &oa, NULL);
  bool bad = false;
  if (w) {                                               /* compare by structure: inside a birth scope ids are not canonical */
    uint8_t kind; uint32_t head; int ar; const Term *args;
    tc_node(tc_term(w), &kind, &head, &ar, &args);
    bad = kind == K_APP && (int)head == W1c && ar == 1;
    printf("    the lemma fired; its made fact has head %s\n", (int)head == W1c ? "W1" : (int)head == B1c ? "B1" : "other");
  }
  HOLDS(!bad, "(a) the installed lemma A1(x) |- B1(x) does not make W1(1)");
  if (bad) printf("    occurrence %u in protected space 1 is W1(1); no rule of the sealed theory makes W1\n", w);
  return 0;
}

static int part_b(void) {
  SETUP(tc_init(1u << 14, 1u << 8));
  NAT = tc_sort(0); THM = tc_sort(SORT_PROVABLE);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  Zc = tc_con((uint16_t)NAT, 0, 0, NULL); Sc = tc_con((uint16_t)NAT, 0, 1, &n1);
  A1c = tc_con((uint16_t)THM, 0, 1, &n1); B1c = tc_con((uint16_t)THM, 0, 1, &n1); W1c = tc_con((uint16_t)THM, 0, 1, &n1);
  Binder w[32];
  for (int i = 0; i < 32; i++) w[i] = (Binder){ (uint16_t)NAT, 0, 0 };
  int WIDE = tc_con((uint16_t)NAT, 0, 32, w);
  SETUP(WIDE >= 0);
  kc_ctx_nat(1);
  Term x = tc_v(0);
  /* a statement checked in a birth scope: BIG(x) |- B1(x), BIG = A1(W(W(W(x,..),..),..)) with W of
     arity 32: three nodes, but its bytecode would need over 32,000 words, past the 4096-word budget */
  tc_birth();
  Term big = x, args[32];
  for (int lvl = 0; lvl < 3; lvl++) { for (int i = 0; i < 32; i++) args[i] = big; big = tc_app(WIDE, args); }
  big = tc_app(A1c, &big);
  Term concl = tc_app(B1c, &x);
  SETUP(big && concl);
  Rule ax = { .nkeep = 1, .keep = { { big, 0 } }, .make = { concl, 0 }, .fresh = -1 };
  int rax = tc_rule(&ax);                                /* trusted axiom, installed in the scope */
  SETUP(rax >= 0);
  /* the next statement: its own terms may take the ids the scope released */
  kc_ctx_nat(1);
  x = tc_v(0);
  tc_birth();
  Term filler = x;
  for (int lvl = 0; lvl < 3; lvl++) { for (int i = 0; i < 32; i++) args[i] = filler; filler = tc_app(WIDE, args); }   /* same count of nodes */
  Term hyp = tc_app(A1c, &x);
  Term want = tc_app(W1c, &x);
  SETUP(hyp && want);
  printf("    ids reused by the next statement: %s\n", hyp == big && want == concl ? "yes" : "no");
  SETUP(tc_lemma(1, 0) && tc_lemma_hyp(hyp));
  Step st = { .kind = ST_RULE, .rule = rax, .prem = { -1 }, .target = want };
  int s0 = tc_lemma_step(&st);
  HOLDS(s0 < 0, "(b) citing the axiom BIG(x) |- B1(x) does not prove A1(x) |- W1(x)");
  if (s0 >= 0) {
    int lem = tc_lemma_end(s0);
    printf("    tc_lemma_step accepted it; tc_lemma_end installed rule %d: A1(x) |- W1(x)\n", lem);
  }
  return 0;
}

int main(void) {
  part_a();
  part_b();
  FINISH("k17_birth_scope_rule");
}
