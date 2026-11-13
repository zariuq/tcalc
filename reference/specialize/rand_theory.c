/* rand_theory.c: writes random theories in the text form of tcs.h, for the differential.
 *
 *   usage: rand_theory SEED THEORIES > FILE.tcs
 *
 * Signature: labels p/1, q/2, r/3, e/0; functions f/1, g/2; constants a, b; codes 0..2; names
 * @0..@3 (the drivers mint @0 and @1 first, so @2 and @3 are minted only by fresh rules).
 * Host guards lt(T, U), isname(T) and maybe(T) are the ones diff_spec registers.
 * Rules draw parameters, takes, reads, makes, tells, told disequations and the guards over
 * a small pool of locals, so repeated locals, nested patterns, static clashes, free guard-only
 * locals and rules outside the fragment (a local left unbound in a make) all occur.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng;
static unsigned rnd(unsigned n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return (unsigned)(rng % n);
}

static int nparams, fresh;
static const char *locals[] = {"A", "B", "C", "D"};

static void term(int depth) {
  unsigned k = rnd(100);
  if (k < 34) fputs(rnd(8) ? locals[rnd(3 + (rnd(3) == 0))] : "_", stdout);
  else if (k < 46 && nparams) printf("P%u", rnd((unsigned)nparams));
  else if (k < 56) printf("%u", rnd(3));
  else if (k < 64) printf("@%u", rnd(4) < 3 ? rnd(2) : 2 + rnd(2));
  else if (k < 72) fputs(rnd(2) ? "a" : "b", stdout);
  else if (k < 77 && fresh) printf("#%u", rnd(10) ? 0 : 1);
  else if (depth > 0) {
    if (rnd(2)) {
      fputs("f(", stdout);
      term(depth - 1);
    } else {
      fputs("g(", stdout);
      term(depth - 1);
      fputs(", ", stdout);
      term(depth - 1);
    }
    fputs(")", stdout);
  } else
    fputs(locals[rnd(3)], stdout);
}

static void label(void) {
  switch (rnd(9)) {
  case 7: term(1); break; /* a bare term: a code, a name, a local (any label), f(..) or g(..) */
  case 8:
  case 0: fputs("e", stdout); break;
  case 1: case 2: fputs("p(", stdout), term(2), fputs(")", stdout); break;
  case 3: case 4: fputs("q(", stdout), term(1), fputs(", ", stdout), term(1), fputs(")", stdout); break;
  default:
    fputs("r(", stdout), term(1), fputs(", ", stdout), term(1), fputs(", ", stdout), term(1), fputs(")", stdout);
    break;
  }
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s SEED THEORIES\n", argv[0]);
    return 2;
  }
  rng = strtoull(argv[1], NULL, 10) * 6364136223846793005ULL + 1442695040888963407ULL;
  long n = strtol(argv[2], NULL, 10);
  for (long t = 0; t < n; t++) {
    printf("theory t%ld\n", t);
    unsigned nrules = 3 + rnd(5);
    for (unsigned i = 0; i < nrules; i++) {
      printf("rule r%u\n", i);
      nparams = (int)rnd(3);
      fresh = rnd(5) == 0 ? 1 : 0;
      if (nparams) {
        fputs("  params", stdout);
        for (int k = 0; k < nparams; k++) printf(" P%d", k);
        fputs("\n", stdout);
      }
      if (fresh) puts("  fresh 1");
      unsigned nt = rnd(3), nr = rnd(3), nm = rnd(3), ntell = rnd(4) == 0 ? 1 + rnd(2) : 0;
      for (unsigned k = 0; k < nt; k++) fputs("  take ", stdout), label(), puts("");
      for (unsigned k = 0; k < nr; k++) fputs("  read ", stdout), label(), puts("");
      for (unsigned k = 0; k < ntell; k++) fputs("  tell ", stdout), term(1), fputs(" = ", stdout), term(1), puts("");
      if (rnd(4) == 0) fputs("  apart ", stdout), term(1), fputs(" = ", stdout), term(1), puts("");
      unsigned ng = rnd(3);
      for (unsigned k = 0; k < ng; k++) {
        unsigned g = rnd(12);
        if (g < 3) fputs("  ask ", stdout), term(1), fputs(" = ", stdout), term(1), puts("");
        else if (g < 6) fputs("  absent ", stdout), label(), puts("");
        else if (g < 9) fputs("  count ", stdout), label(), printf(" = %u\n", rnd(3));
        else if (g < 10) fputs("  host lt(", stdout), term(1), fputs(", ", stdout), term(1), puts(")");
        else if (g < 11) fputs("  host isname(", stdout), term(1), puts(")");
        else fputs("  host maybe(", stdout), term(1), puts(")");
      }
      for (unsigned k = 0; k < nm; k++) fputs("  make ", stdout), label(), puts("");
      /* a minted name shows only where it is made (in a pattern or a tell it clashes) */
      if (fresh && rnd(2)) fputs("  make ", stdout), puts(rnd(2) ? "p(#0)" : "q(#0, a)");
      puts("end");
    }
  }
  return 0;
}
