/* sieve_spec.c: the CHR prime sieve of tcalc_ref's bench.c, as the rules of sieve.tcs, on the
 * generated code and on the generic route; the control layer (which firing to try next) is
 * bench.c's.  Both routes must find the same primes and end in tr_state_equal states.
 *
 *   usage: sieve_spec N...
 */
#include "tcs.h"

#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}
static long max_rss_kb(void) {
  struct rusage u;
  getrusage(RUSAGE_SELF, &u);
  return u.ru_maxrss;
}

static int h_gt1(tr_view *v, const tr_term *a, size_t n) {
  int64_t x;
  return n == 1 && tr_view_code(v, a[0], &x) && x > 1;
}
static int h_pred(tr_view *v, const tr_term *a, size_t n) {
  int64_t x, y;
  return n == 2 && tr_view_code(v, a[0], &x) && tr_view_code(v, a[1], &y) && y == x - 1;
}
static int h_divides(tr_view *v, const tr_term *a, size_t n) {
  int64_t y, x;
  return n == 2 && tr_view_code(v, a[0], &y) && tr_view_code(v, a[1], &x) && y != 0 && x % y == 0;
}

typedef struct {
  bool generic;
  const tcs_compiled_rule *cand, *absorb;
  const tcs_rule *scand, *sabsorb;
  tcs_instance inst;
} route;

static tr_verdict fire(route *m, tr_state *s, bool absorb, const tr_term *p, const tr_occ *o, tr_result *r) {
  if (m->generic)
    return tr_fire(s, tcs_instance_of(&m->inst, tr_state_ctx(s), absorb ? m->sabsorb : m->scand, p, o), r);
  return (absorb ? m->absorb : m->cand)->decide(s, p, o, r, true);
}

/* Returns the state; *primes the number of primes found, *firings the decisions. */
static tr_state *sieve(tr_ctx *c, route *m, int64_t n, size_t *firings, double *secs) {
  tr_state *s = tr_state_new(c);
  uint32_t candidate = tr_symbol(c, "candidate", 1), prime = tr_symbol(c, "prime", 1);
  tr_term X = tr_local(c, 0), primeX = tr_app(c, prime, &X);
  double t0 = now();
  tr_term start = tr_code(c, n);
  tr_make m0 = {tr_app(c, candidate, &start), 0, 0};
  tr_firing init = {.makes = &m0, .nmakes = 1};
  tr_occ cand = 0;
  tr_result r0 = {.made = &cand};
  tr_fire(s, &init, &r0);
  size_t count = 0;
  for (;;) { /* candidate(N) <=> N > 1 | prime(N), candidate(N-1) */
    tr_term label;
    if (!tr_present(s, cand, &label)) break;
    tr_term next = tr_code(c, tr_term_code(c, tr_term_arg(c, label, 0)) - 1);
    tr_occ made[2];
    tr_result r = {.made = made};
    count++;
    if (fire(m, s, false, &next, &cand, &r) != TR_ADMITTED) break;
    cand = made[1];
  }
  size_t np = tr_present_count(s) + 1, nx = 0; /* prime(Y) \ prime(X) <=> X mod Y =:= 0 | true */
  tr_occ *xs = malloc(np * sizeof *xs);
  for (tr_occ o = tr_next_candidate(s, primeX, 0, NULL); o; o = tr_next_candidate(s, primeX, o, NULL)) xs[nx++] = o;
  for (size_t i = 0; i < nx; i++)
    for (tr_occ y = tr_next_candidate(s, primeX, 0, NULL); y; y = tr_next_candidate(s, primeX, y, NULL)) {
      if (y == xs[i]) continue;
      tr_occ o[2] = {xs[i], y};
      count++;
      if (fire(m, s, true, NULL, o, NULL) == TR_ADMITTED) break;
    }
  *secs = now() - t0;
  free(xs);
  *firings = count;
  return s;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s N...\n", argv[0]);
    return 2;
  }
  const tcs_host hosts[] = {{"gt1", h_gt1}, {"pred", h_pred}, {"divides", h_divides}};
  tcs_register_hosts(hosts, 3);
  const tcs_compiled_theory *T = NULL;
  for (size_t i = 0; i < tcs_ncompiled; i++)
    if (!strcmp(tcs_compiled[i].name, "sieve")) T = &tcs_compiled[i];
  int rc = 0;
  for (int a = 1; a < argc; a++) {
    int64_t n = strtoll(argv[a], NULL, 10);
    tr_ctx *c = tr_ctx_new();
    if (!T || !T->link(c)) return 2;
    route m[2];
    for (int k = 0; k < 2; k++) {
      memset(&m[k], 0, sizeof m[k]);
      m[k].generic = k == 1;
      m[k].cand = &T->rules[0], m[k].absorb = &T->rules[1];
      m[k].scand = tcs_find(T->schemas(), "candidate"), m[k].sabsorb = tcs_find(T->schemas(), "absorb");
    }
    size_t f[2];
    double t[2];
    size_t fast0 = tcs_count.fast;
    tr_state *s[2] = {sieve(c, &m[0], n, &f[0], &t[0]), sieve(c, &m[1], n, &f[1], &t[1])};
    size_t primes = 0;
    bool all_prime = true;
    tr_term l;
    for (tr_occ o = tr_next_present(s[0], 0, &l); o; o = tr_next_present(s[0], o, &l)) {
      if (strcmp(tr_symbol_name(c, tr_term_symbol(c, l)), "prime")) continue;
      int64_t p = tr_term_code(c, tr_term_arg(c, l, 0));
      for (int64_t d = 2; d * d <= p; d++) all_prime &= p % d != 0;
      primes++;
    }
    bool same = tr_state_equal(s[0], s[1]) && f[0] == f[1];
    printf("sieve %lld: %zu primes (%s); %zu decisions on each route (%zu on the specialized path); generated %.3f s (%.0f ns "
           "per decision), generic route %.3f s (%.0f ns), %.1fx; states %s; max RSS %ld KB\n",
           (long long)n, primes, all_prime ? "all prime" : "WRONG", f[0], tcs_count.fast - fast0, t[0], 1e9 * t[0] / (double)f[0],
           t[1], 1e9 * t[1] / (double)f[1], t[1] / t[0], same ? "equal" : "DIFFERENT", max_rss_kb());
    rc |= !same || !all_prime;
    for (int k = 0; k < 2; k++) {
      tcs_instance_free(&m[k].inst);
      tr_state_free(s[k]);
    }
    tr_ctx_free(c);
  }
  return rc;
}
