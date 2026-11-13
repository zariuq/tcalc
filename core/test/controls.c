/* Controls of the tc0 kernel: one function per guarantee in tc0.h.  Each prints "holds" or
   "VIOLATED" with the reason; the exit status is the number of violated guarantees.
   Adapted from the tcalc kernel controls that apply to this fragment (k04 and k29: names minted
   before use; k15, k22, k25: a refused firing changes nothing; k24: hostile ids; k31: table growth;
   k34: one meaning of the destination; k01, k13: the seal). */
#include <stdio.h>
#include <string.h>
#include "tc0.h"

static int violated;
static bool ok_all;
static void check(bool c, const char *what) { if (!c) { printf("    not so: %s\n", what); ok_all = false; } }
static void report(const char *name) { printf("%s %s\n", ok_all ? "holds   " : "VIOLATED", name); if (!ok_all) violated++; ok_all = true; }

static int A1, B2, W0, F2;
static void theory(void) {
  tc0_init(1u << 16);
  A1 = tc0_con(1); B2 = tc0_con(2); W0 = tc0_con(0); F2 = tc0_con(2);
}
static Term app1(int c, Term a) { return tc0_app(c, &a); }
static Term app2(int c, Term a, Term b) { Term t[2] = { a, b }; return tc0_app(c, t); }

/* k04, k29: a caller cannot hold a generative name before it is minted, and a structural code never
   equals a minted name, so a fresh name is new to the whole state.  The scene has no take (Gemini's):
   R1 |- A(x) for a caller-given x;  R2: keep A(x), fresh n |- B(x, n);  R3: keep B(x, x) |- W.
   No run derives W: n is minted after A(x) exists, so x and n differ. */
static void names_minted_before_use(void) {
  theory();
  Term x = tc0_hole(0), n = tc0_hole(1);
  Term ax = app1(A1, x), bxn = app2(B2, x, n), bxx = app2(B2, x, x), w = tc0_app(W0, NULL);
  int r1 = tc0_rule(0, NULL, ax, -1, NULL), r2 = tc0_rule(1, &ax, bxn, 1, NULL), r3 = tc0_rule(1, &bxx, w, -1, NULL);
  uint8_t gen_only[TC0_HOLES] = { TC0_GEN_ONLY };
  int r4 = tc0_rule(0, NULL, ax, -1, gen_only);                 /* |- A(x) for a minted x only */
  tc0_seal();
  check(r1 >= 0 && r2 >= 0 && r3 >= 0 && r4 >= 0, "the rules are admitted");
  check(tc0_gen(0) == 0, "no generative name exists before the first mint");
  Term in[TC0_HOLES] = { [0] = tc0_code(0) };                   /* the code of the id the next mint takes */
  check(tc0_fire(r1, NULL, in, 0), "R1 accepts a structural code");
  check(!tc0_fire(r4, NULL, in, 9), "a hole for minted names refuses a structural code");
  uint64_t k0 = 0;
  check(tc0_fire(r2, &k0, NULL, 1), "R2 fires on A(code 0) and mints a name");
  const Term *b = tc0_args(tc0_slot(1), NULL, NULL);
  check(b && tc0_kind(b[1]) == TC0_K_GEN && tc0_id(b[1]) == 0 && b[0] != b[1], "the minted name 0 differs from the code 0");
  uint64_t k1 = 1;
  check(!tc0_fire(r3, &k1, NULL, 2), "W is not derived");
  Term g0 = tc0_gen(0);
  Term in2[TC0_HOLES] = { [0] = g0 };
  check(g0 && tc0_fire(r4, NULL, in2, 3), "once minted, the name is accepted where only minted names are");
  check(tc0_fire(r1, NULL, in2, 4), "R1 accepts the minted name");
  uint64_t k4 = 4;
  check(tc0_fire(r2, &k4, NULL, 5), "R2 fires on A(name 0)");
  b = tc0_args(tc0_slot(5), NULL, NULL);
  check(b && b[0] == g0 && tc0_id(b[1]) == 1, "the next mint is name 1, new to the state");
  uint64_t k5 = 5;
  check(!tc0_fire(r3, &k5, NULL, 6), "W is still not derived");
  report("names_minted_before_use");
}

/* Structural ids need no minting and equal terms have equal ids, also after the tables grow. */
static void structural_ids(void) {
  theory();
  Term c7 = tc0_code(7), f = app2(F2, c7, c7);
  check(c7 && c7 == tc0_code(7), "equal codes are one term");
  check(f && f == app2(F2, tc0_code(7), tc0_code(7)), "equal applications are one term");
  Term g = tc0_mint();
  check(g && g != tc0_code(tc0_id(g)), "a minted name is not the code of its id");
  for (uint64_t i = 0; i < 300000; i++) if (!tc0_code(1000 + i)) { check(false, "growth"); break; }
  check(tc0_code(7) == c7 && app2(F2, c7, c7) == f && tc0_gen(0) == g, "terms keep their ids when the tables grow");
  check(tc0_code(1000 + 299999) == tc0_code(1000 + 299999), "the last code made is found again");
  report("structural_ids");
}

/* k15, k22, k25: every refused firing leaves the slots and the name counter as they were, and a valid
   firing after it is admitted. */
static void refusal_changes_nothing(void) {
  theory();
  Term x = tc0_hole(0), y = tc0_hole(1), n = tc0_hole(2);
  Term fxy = app2(F2, x, y), fyx = app2(F2, y, x), fxx = app2(F2, x, x);
  uint8_t gen_only[TC0_HOLES] = { TC0_GEN_ONLY };
  int sym = tc0_rule(1, &fxy, fyx, -1, NULL);                   /* keep F(x,y) |- F(y,x) */
  int dia = tc0_rule(1, &fxx, app1(A1, x), -1, NULL);           /* keep F(x,x) |- A(x) */
  int mk = tc0_rule(0, NULL, app2(B2, x, n), 2, gen_only);      /* fresh n |- B(x, n), x minted */
  tc0_seal();
  Term g = tc0_mint();
  tc0_put(0, app2(F2, tc0_code(1), tc0_code(2)));
  tc0_put(1, app1(A1, tc0_code(3)));
  Term before[4]; for (int s = 0; s < 4; s++) before[s] = tc0_slot((uint64_t)s);
  uint64_t last = tc0_last_gen();
  uint64_t k0 = 0, k1 = 1;
  Term code_in[TC0_HOLES] = { [0] = tc0_code(5) }, none[TC0_HOLES] = { 0 };
  bool r[6] = {
    tc0_fire(dia, &k0, NULL, 2),                                /* F(1,2) is not F(x,x) */
    tc0_fire(sym, &k1, NULL, 2),                                /* slot 1 holds an A fact */
    tc0_fire(mk, NULL, code_in, 2),                             /* x must be a minted name */
    tc0_fire(mk, NULL, none, 2),                                /* x not given */
    tc0_fire(mk, NULL, NULL, 2),
    tc0_fire(sym, &k0, NULL, UINT64_MAX),                       /* no such slot */
  };
  for (int i = 0; i < 6; i++) check(!r[i], "the firing is refused");
  bool same = tc0_last_gen() == last;
  for (int s = 0; s < 4; s++) same &= tc0_slot((uint64_t)s) == before[s];
  check(same, "slots and name counter are unchanged");
  Term gin[TC0_HOLES] = { [0] = g };
  check(tc0_fire(sym, &k0, NULL, 2) && tc0_fire(mk, NULL, gin, 3), "valid firings are admitted afterwards");
  check(tc0_last_gen() == last + 1, "the valid fresh firing minted exactly one name");
  report("refusal_changes_nothing");
}

/* k24: ids from a hostile caller are refused or read as nothing; they never crash. */
static void hostile_ids(void) {
  theory();
  Term x = tc0_hole(0), fxx = app2(F2, x, x);
  int r = tc0_rule(1, &fxx, app1(A1, x), -1, NULL), p = tc0_rule(0, NULL, app1(A1, x), -1, NULL);
  Term in[TC0_HOLES] = { [0] = tc0_code(1) };
  check(tc0_default(p, in), "a default fact A(1)");
  tc0_seal();
  uint64_t far = UINT64_MAX;
  check(!tc0_fire(-1, NULL, NULL, 0) && !tc0_fire(99, NULL, NULL, 0), "unknown rules are refused");
  check(!tc0_fire(r, &far, NULL, 0), "a premise read from an unwritten slot is the default fact, A(1), not F(x,x)");
  Term bad[3] = { 0, 1u << 30, x };
  for (int i = 0; i < 3; i++) { Term b[TC0_HOLES] = { [0] = bad[i] }; check(!tc0_fire(p, NULL, b, 0), "a missing, unknown or open input is refused"); }
  check(!tc0_put(0, x) && !tc0_put(0, fxx) && !tc0_put(0, 1u << 30) && !tc0_put(0, tc0_code(4)), "only ground applications can be put");
  Term args[2] = { 0, 1u << 30 };
  check(!tc0_app(-1, args) && !tc0_app(F2, args) && !tc0_args(0, NULL, NULL) && !tc0_args(1u << 30, NULL, NULL), "bad constructors and arguments are refused");
  check(tc0_kind(1u << 30) == 0 && tc0_id(x) == 0, "unknown terms have no kind and holes no id");
  report("hostile_ids");
}

/* k01, k13: after the seal the theory cannot change. */
static void seal(void) {
  theory();
  Term x = tc0_hole(0);
  int p = tc0_rule(0, NULL, app1(A1, x), -1, NULL);
  tc0_seal();
  Term in[TC0_HOLES] = { [0] = tc0_code(1) };
  check(tc0_con(1) < 0 && tc0_rule(0, NULL, app1(A1, x), -1, NULL) < 0 && !tc0_default(p, in), "no constructor, rule or default after the seal");
  check(tc0_fire(p, NULL, in, 0), "firing goes on");
  report("seal");
}

/* k34: the destination slot is replaced by the conclusion; a rule may write a slot it reads. */
static void dest_one_meaning(void) {
  theory();
  Term x = tc0_hole(0), y = tc0_hole(1), fxy = app2(F2, x, y);
  int sym = tc0_rule(1, &fxy, app2(F2, y, x), -1, NULL);
  tc0_seal();
  tc0_put(0, app2(F2, tc0_code(1), tc0_code(2)));
  uint64_t k0 = 0;
  check(tc0_fire(sym, &k0, NULL, 0), "the rule writes the slot it read");
  check(tc0_slot(0) == app2(F2, tc0_code(2), tc0_code(1)), "the slot holds the conclusion");
  check(tc0_fire(sym, &k0, NULL, 0) && tc0_slot(0) == app2(F2, tc0_code(1), tc0_code(2)), "and again");
  report("dest_one_meaning");
}

/* Rules are flat, fresh names never occur in premises, and the shapes are bounded. */
static void rule_shapes(void) {
  theory();
  Term x = tc0_hole(0), n = tc0_hole(1), ax = app1(A1, x);
  Term nested = app1(A1, ax), an = app1(A1, n), k5[5] = { ax, ax, ax, ax, ax };
  check(tc0_rule(0, NULL, nested, -1, NULL) < 0, "a nested conclusion is refused");
  check(tc0_rule(1, &nested, ax, -1, NULL) < 0, "a nested premise is refused");
  check(tc0_rule(1, &an, app2(B2, n, x), 1, NULL) < 0, "a fresh hole in a premise is refused");
  check(tc0_rule(0, NULL, ax, 1, NULL) < 0, "a fresh hole the conclusion does not use is refused");
  check(tc0_rule(5, k5, ax, -1, NULL) < 0, "more than four premises are refused");
  check(tc0_rule(4, k5, ax, -1, NULL) >= 0, "four premises are admitted");
  report("rule_shapes");
}

int main(void) {
  ok_all = true;
  names_minted_before_use();
  structural_ids();
  refusal_changes_nothing();
  hostile_ids();
  seal();
  dest_one_meaning();
  rule_shapes();
  printf("tc0 controls: %d of 7 violated\n", violated);
  return violated;
}
