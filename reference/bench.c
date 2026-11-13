/* bench.c: two clients of tcalc_ref with their times and memory.
 *
 *   bench sieve N    the CHR prime sieve: candidate(N) <=> N > 1 | prime(N), candidate(N-1);
 *                    prime(Y) \ prime(X) <=> X mod Y =:= 0 | true.  Prints the primes found.
 *   bench store N M [new|known]
 *                    a store of N items; M firings each take one item, read a config fact,
 *                    check the absence of `stop` and that exactly one config fact is present,
 *                    and make an item with a new label (a new term) or a known one.  The cost of
 *                    a firing should not grow with N.
 *
 * The control layer (which firing to try next) is here; every firing is decided by tr_fire.
 */
#include "tcalc_ref.h"

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

/* Host guards: their terms are written as in the firing (locals 0 and 1). */
static int greater_than_one(tr_view *v, void *env) {
  int64_t n;
  return tr_view_code(v, *(tr_term *)env, &n) && n > 1;
}
static int divides(tr_view *v, void *env) {
  tr_term *xy = env;
  int64_t x, y;
  return tr_view_code(v, xy[0], &x) && tr_view_code(v, xy[1], &y) && y != 0 && x % y == 0;
}

static int sieve(int64_t n) {
  tr_ctx *c = tr_ctx_new();
  tr_state *s = tr_state_new(c);
  uint32_t prime = tr_symbol(c, "prime", 1), candidate = tr_symbol(c, "candidate", 1);
  tr_term X = tr_local(c, 0), Y = tr_local(c, 1);
  tr_term primeX = tr_app(c, prime, &X), primeY = tr_app(c, prime, &Y), candX = tr_app(c, candidate, &X);
  size_t admitted = 0, refused = 0;
  double t0 = now();

  /* candidate(n) */
  tr_term start = tr_code(c, n);
  tr_make m0 = {tr_app(c, candidate, &start), 0, 0};
  tr_firing init = {.makes = &m0, .nmakes = 1};
  tr_occ cand = 0;
  tr_result r = {.made = &cand};
  tr_fire(s, &init, &r);

  /* candidate(N) <=> N > 1 | prime(N), candidate(N-1): the control layer computes N-1 */
  for (;;) {
    tr_term label;
    if (!tr_present(s, cand, &label)) break;
    int64_t k = tr_term_code(c, tr_term_arg(c, label, 0));
    tr_term next = tr_code(c, k - 1);
    tr_use take = {candX, cand};
    tr_make makes[2] = {{primeX, 0, 0}, {tr_app(c, candidate, &next), 0, 0}};
    tr_guard g = {.kind = TR_G_HOST, .entailed = greater_than_one, .env = &X};
    tr_firing f = {.locals = 1, .takes = &take, .ntakes = 1, .makes = makes, .nmakes = 2, .guards = &g, .nguards = 1};
    tr_occ made[2];
    tr_result rr = {.made = made};
    if (tr_fire(s, &f, &rr) != TR_ADMITTED) { refused++; break; }
    admitted++;
    cand = made[1];
  }
  double t1 = now();

  /* prime(Y) \ prime(X) <=> X mod Y =:= 0 | true: for each X, its partners from the head index */
  size_t np = tr_present_count(s) + 1, nx = 0;
  tr_occ *xs = malloc(np * sizeof *xs);
  for (tr_occ o = tr_next_candidate(s, primeX, 0, NULL); o; o = tr_next_candidate(s, primeX, o, NULL)) xs[nx++] = o;
  tr_term xy[2] = {X, Y};
  tr_guard g = {.kind = TR_G_HOST, .entailed = divides, .env = xy};
  for (size_t i = 0; i < nx; i++) {
    tr_occ x = xs[i];
    for (tr_occ y = tr_next_candidate(s, primeY, 0, NULL); y; y = tr_next_candidate(s, primeY, y, NULL)) {
      if (y == x) continue;
      tr_use take = {primeX, x}, read = {primeY, y};
      tr_firing f = {.locals = 2, .takes = &take, .ntakes = 1, .reads = &read, .nreads = 1, .guards = &g, .nguards = 1};
      if (tr_fire(s, &f, NULL) == TR_ADMITTED) { admitted++; break; }
      refused++;
    }
  }
  double t2 = now();
  size_t primes = 0, ok = 1;
  tr_term l;
  for (tr_occ o = tr_next_present(s, 0, &l); o; o = tr_next_present(s, o, &l)) {
    if (tr_term_symbol(c, l) != prime) continue;
    int64_t p = tr_term_code(c, tr_term_arg(c, l, 0));
    for (int64_t d = 2; d * d <= p; d++) ok &= p % d != 0;
    primes++;
  }
  printf("sieve %lld: %zu primes (%s); firings admitted %zu, refused %zu; candidates %.3fs, absorb %.3fs, "
         "total %.3fs (%.0f ns per firing); terms %zu; max RSS %ld KB\n",
         (long long)n, primes, ok ? "all prime" : "WRONG", admitted, refused, t1 - t0, t2 - t1, t2 - t0,
         1e9 * (t2 - t0) / (double)(admitted + refused), tr_ctx_terms(c), max_rss_kb());
  free(xs);
  tr_state_free(s);
  tr_ctx_free(c);
  return ok ? 0 : 1;
}

static int store(size_t n, size_t m, bool fresh) {
  tr_ctx *c = tr_ctx_new();
  tr_state *s = tr_state_new(c);
  uint32_t item = tr_symbol(c, "item", 1);
  tr_term cfg = tr_const(c, "cfg"), stop = tr_const(c, "stop"), I = tr_local(c, 0);
  tr_term itemI = tr_app(c, item, &I);
  tr_occ *ids = malloc((n + 1) * sizeof *ids);
  double t0 = now();
  tr_occ cfgid = 0;
  {
    tr_make mk = {cfg, 0, 0};
    tr_firing f = {.makes = &mk, .nmakes = 1};
    tr_result r = {.made = &cfgid};
    tr_fire(s, &f, &r);
  }
  for (size_t i = 0; i < n; i++) {
    tr_term v = tr_code(c, (int64_t)i);
    tr_make mk = {tr_app(c, item, &v), 0, 0};
    tr_firing f = {.makes = &mk, .nmakes = 1};
    tr_result r = {.made = &ids[i]};
    tr_fire(s, &f, &r);
  }
  double t1 = now();
  size_t admitted = 0;
  for (size_t j = 0; j < m; j++) {
    size_t k = (j * 7919) % n;
    tr_term v = tr_code(c, (int64_t)(fresh ? n + j : (j * 31) % n)); /* a new term, or a known one */
    tr_use take = {itemI, ids[k]}, read = {cfg, cfgid};
    tr_make mk = {tr_app(c, item, &v), 0, 0};
    tr_guard g[2] = {{.kind = TR_G_ABSENT, .a = stop}, {.kind = TR_G_COUNT, .a = cfg, .number = 1}};
    tr_firing f = {.locals = 1, .takes = &take, .ntakes = 1, .reads = &read, .nreads = 1,
                   .makes = &mk, .nmakes = 1, .guards = g, .nguards = 2};
    tr_result r = {.made = &ids[k]};
    admitted += tr_fire(s, &f, &r) == TR_ADMITTED;
  }
  double t2 = now();
  printf("store %zu items, %zu firings making %s labels: %zu admitted, present %zu, terms %zu; load %.3fs, "
         "firings %.3fs (%.0f ns per firing); max RSS %ld KB\n",
         n, m, fresh ? "new" : "known", admitted, tr_present_count(s), tr_ctx_terms(c), t1 - t0, t2 - t1,
         1e9 * (t2 - t1) / (double)m, max_rss_kb());
  free(ids);
  tr_state_free(s);
  tr_ctx_free(c);
  return admitted != m;
}

int main(int argc, char **argv) {
  if (argc >= 3 && !strcmp(argv[1], "sieve")) return sieve(strtoll(argv[2], NULL, 10));
  if (argc >= 4 && !strcmp(argv[1], "store"))
    return store(strtoull(argv[2], NULL, 10), strtoull(argv[3], NULL, 10), argc < 5 || strcmp(argv[4], "known"));
  fprintf(stderr, "usage: %s sieve N | store N M [new|known]\n", argv[0]);
  return 2;
}
