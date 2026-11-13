/* tcs_roundtrip.c: rules as the reference's own data, and the text form, agree.
 *   1. Micromath's substitute1 and the sieve's two rules, written as tr_firing schemas in C, become a
 *      theory (tcs_theory_from_firings); written as text (tcs_write) and read back (tcs_read), every
 *      term is the same term (hash-consed: the same id) and every instance the same firing.
 *   2. Every theory of the .tcs files given is read, written, read again, and compared the same way.
 *   usage: tcs_roundtrip [FILE.tcs ...]
 */
#include "tcs.h"

#include <stdlib.h>
#include <string.h>

static long bad;

static void check(bool ok, const char *what) {
  if (!ok && bad++ < 10) fprintf(stderr, "differs: %s\n", what);
}

static bool same_rule(const tcs_rule *a, const tcs_rule *b) {
  bool ok = !strcmp(a->name, b->name) && a->nparams == b->nparams && a->nlocals == b->nlocals && a->fresh == b->fresh &&
            a->ntakes == b->ntakes && a->nreads == b->nreads && a->nmakes == b->nmakes && a->ntells == b->ntells &&
            a->napart == b->napart && a->nguards == b->nguards;
  for (size_t i = 0; ok && i < a->ntakes; i++) ok = a->takes[i] == b->takes[i];
  for (size_t i = 0; ok && i < a->nreads; i++) ok = a->reads[i] == b->reads[i];
  for (size_t i = 0; ok && i < a->nmakes; i++) ok = a->makes[i] == b->makes[i];
  for (size_t i = 0; ok && i < a->ntells; i++) ok = a->tells[i].left == b->tells[i].left && a->tells[i].right == b->tells[i].right;
  for (size_t i = 0; ok && i < a->napart; i++) ok = a->apart[i].left == b->apart[i].left && a->apart[i].right == b->apart[i].right;
  for (size_t i = 0; ok && i < a->nguards; i++)
    ok = a->guards[i].kind == b->guards[i].kind && a->guards[i].a == b->guards[i].a && a->guards[i].b == b->guards[i].b &&
         a->guards[i].number == b->guards[i].number;
  return ok;
}

/* Write, read back, compare; returns the rules compared. */
static size_t roundtrip(tr_ctx *c, const tcs_theory *th, int n, const char *what) {
  char *text = NULL;
  size_t len = 0;
  FILE *f = open_memstream(&text, &len);
  check(f && tcs_write(f, c, th, n), what);
  if (f) fclose(f);
  tcs_theory *back = NULL;
  char err[256];
  int m = text ? tcs_read(c, text, &back, err, sizeof err) : -1;
  if (m != n) {
    fprintf(stderr, "%s: read back %d theories (%s)\n", what, m, m < 0 ? err : "");
    bad++;
    free(text);
    return 0;
  }
  size_t rules = 0;
  for (int t = 0; t < n; t++) {
    check(back[t].nrules == th[t].nrules && !strcmp(back[t].name, th[t].name), what);
    for (size_t r = 0; r < th[t].nrules && r < back[t].nrules; r++, rules++) check(same_rule(&th[t].rules[r], &back[t].rules[r]), th[t].rules[r].name);
  }
  tcs_free(back, m);
  free(text);
  return rules;
}

static tr_term rd(tr_ctx *c, tr_scope *sc, const char *s) {
  tr_term t = tr_read(c, sc, s);
  if (t == TR_NONE) {
    fprintf(stderr, "cannot read %s\n", s);
    exit(2);
  }
  return t;
}

int main(int argc, char **argv) {
  tr_ctx *c = tr_ctx_new();
  /* 1. firings as schemas */
  tr_scope *s1 = tr_scope_new(), *s2 = tr_scope_new(), *s3 = tr_scope_new();
  /* substitute1: no parameters; the side conditions are repeated locals */
  tr_use r1[4] = {{rd(c, s1, "thm(X, T, U, W)"), 0}, {rd(c, s1, "thm(U1, U, A, B)"), 0}, {rd(c, s1, "thm(W1, W, A, B)"), 0},
                  {rd(c, s1, "thm(X1, X, A, B)"), 0}};
  tr_make m1 = {rd(c, s1, "thm(X1, T, U1, W1)"), 0, 0};
  /* the sieve's candidate rule: parameter M (LOCAL 0) read first, so it gets index 0 */
  rd(c, s2, "M");
  tr_use t2 = {rd(c, s2, "candidate(N)"), 0};
  tr_term gt1_args[1] = {rd(c, s2, "N")}, pred_args[2] = {rd(c, s2, "N"), rd(c, s2, "M")};
  tcs_host_ref h_gt1 = {"gt1", gt1_args, 1}, h_pred = {"pred", pred_args, 2};
  tr_guard g2[2] = {{.kind = TR_G_HOST, .entailed = tcs_named_host, .env = &h_gt1},
                    {.kind = TR_G_HOST, .entailed = tcs_named_host, .env = &h_pred}};
  tr_make m2[2] = {{rd(c, s2, "prime(N)"), 0, 0}, {rd(c, s2, "candidate(M)"), 0, 0}};
  /* the sieve's absorb rule */
  tr_use t3 = {rd(c, s3, "prime(X)"), 0}, r3 = {rd(c, s3, "prime(Y)"), 0};
  tr_term div_args[2] = {rd(c, s3, "Y"), rd(c, s3, "X")};
  tcs_host_ref h_div = {"divides", div_args, 2};
  tr_guard g3 = {.kind = TR_G_HOST, .entailed = tcs_named_host, .env = &h_div};
  tr_firing fs[3] = {
      {.locals = tr_scope_size(s1), .reads = r1, .nreads = 4, .makes = &m1, .nmakes = 1},
      {.locals = tr_scope_size(s2), .takes = &t2, .ntakes = 1, .makes = m2, .nmakes = 2, .guards = g2, .nguards = 2},
      {.locals = tr_scope_size(s3), .takes = &t3, .ntakes = 1, .reads = &r3, .nreads = 1, .guards = &g3, .nguards = 1}};
  const char *names[3] = {"substitute1", "candidate", "absorb"};
  uint32_t np[3] = {0, 1, 0};
  char err[256];
  tcs_theory *th = tcs_theory_from_firings(c, "from_firings", 3, names, fs, np, err, sizeof err);
  if (!th) {
    fprintf(stderr, "%s\n", err);
    return 1;
  }
  size_t n1 = roundtrip(c, th, 1, "theory from firings");
  /* an instance of the firing-built candidate rule equals the instance of the one read from text */
  {
    tcs_instance a = {0};
    tr_term p = tr_code(c, 6);
    tr_occ o = 3;
    const tr_firing *fa = tcs_instance_of(&a, c, &th->rules[1], &p, &o);
    check(fa->locals == 1 && fa->ntakes == 1 && fa->takes[0].occ == 3 && fa->nmakes == 2 && fa->nguards == 2 &&
              fa->makes[1].label == tr_app(c, tr_symbol(c, "candidate", 1), &p),
          "instance of the candidate rule");
    tcs_instance_free(&a);
  }
  /* a firing that is no schema is refused */
  {
    tr_make bad_make = {rd(c, s1, "thm(X, X, X, X)"), 7, 0};
    tr_firing nf = {.locals = 1, .makes = &bad_make, .nmakes = 1};
    tcs_rule r;
    check(!tcs_rule_from_firing(c, "bad", &nf, 0, &r, err, sizeof err), "a make with an identity refused");
  }
  tcs_free(th, 1);
  tr_scope_free(s1), tr_scope_free(s2), tr_scope_free(s3);
  /* 2. theories from files */
  size_t n2 = 0, nth = 0;
  for (int a = 1; a < argc; a++) {
    FILE *f = fopen(argv[a], "rb");
    if (!f) return 2;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *text = malloc((size_t)sz + 1);
    if (!text || fread(text, 1, (size_t)sz, f) != (size_t)sz) return 2;
    fclose(f);
    text[sz] = 0;
    tcs_theory *t;
    int n = tcs_read(c, text, &t, err, sizeof err);
    free(text);
    if (n < 0) {
      fprintf(stderr, "%s: %s\n", argv[a], err);
      return 2;
    }
    n2 += roundtrip(c, t, n, argv[a]);
    nth += (size_t)n;
    tcs_free(t, n);
  }
  printf("tcs_roundtrip: %zu rules built from tr_firing schemas, %zu rules of %zu theories from files: written, read "
         "back, the same terms; %ld differences\n",
         n1, n2, nth, bad);
  tr_ctx_free(c);
  return bad != 0;
}
