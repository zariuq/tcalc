/* k31: a failed growth of the term arena leaves the kernel consistent.
   grow() raises the node capacity before it allocates the larger hash table. When that allocation
   fails, the capacity stays raised and the table does not grow; after two such failures the table can
   fill completely, and the next lookup or insertion probes forever.
   The control caps the address space (setrlimit) so that the table's allocation fails twice while the
   node arrays still grow, then keeps making distinct terms. Repository build only. */
#include "kc.h"
#include <sys/resource.h>

static long vm_bytes(void) {
  FILE *f = fopen("/proc/self/statm", "r");
  long pages = 0;
  if (!f) return -1;
  if (fscanf(f, "%ld", &pages) != 1) pages = -1;
  fclose(f);
  return pages < 0 ? -1 : pages * sysconf(_SC_PAGESIZE);
}
static void cap(long extra) {
  struct rlimit rl;
  getrlimit(RLIMIT_AS, &rl);
  rl.rlim_cur = (rlim_t)(vm_bytes() + extra);
  setrlimit(RLIMIT_AS, &rl);
}
static void uncap(void) {
  struct rlimit rl;
  getrlimit(RLIMIT_AS, &rl);
  rl.rlim_cur = rl.rlim_max;
  setrlimit(RLIMIT_AS, &rl);
}

static Term chain;                                          /* S^k(Z): one new node per step */
static long made;
static bool make_until(long target) {
  while (made < target) {
    Term t = kc_s(chain);
    if (!t) return false;
    chain = t; made++;
  }
  return true;
}
static void fill_past_capacity(void) {
  /* past the second failed growth: the table has as many slots as the arena may now hold nodes */
  alarm(20);
  for (long i = 0; i < (1L << 19); i++) { Term t = kc_s(chain); if (t) { chain = t; made++; } }
  printf("    made %ld nodes after the failures\n", made);
  alarm(0);
}

int main(void) {
  SETUP(tc_init(1u << 16, 1u << 8));                        /* 65,536 nodes; table 262,144 slots */
  NAT = tc_sort(0);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  Zc = tc_con((uint16_t)NAT, 0, 0, NULL); Sc = tc_con((uint16_t)NAT, 0, 1, &n1);
  SETUP(Zc >= 0 && Sc >= 0);
  chain = kc_z(); made = 1;
  SETUP(make_until((1L << 16) - 512));                    /* the arena also holds 64 query unknowns */
  /* first growth (65,536 -> 131,072 nodes): the arrays grow by about 3 MiB, the table needs 2 MiB */
  long v0 = vm_bytes();
  cap(3L << 20 | 512L << 10);
  bool ok1 = make_until((1L << 16) + 64);
  uncap();
  printf("    first capped growth: address space %+ld KiB\n", (vm_bytes() - v0) >> 10);
  SETUP(make_until((1L << 17) - 512));
  /* second growth (131,072 -> 262,144 nodes): the arrays grow by about 6 MiB, the table needs 2 MiB */
  long v1 = vm_bytes();
  cap(6L << 20 | 512L << 10);
  bool ok2 = make_until((1L << 17) + 64);
  uncap();
  printf("    second capped growth: address space %+ld KiB\n", (vm_bytes() - v1) >> 10);
  SETUP(make_until((1L << 18) - 512));
  /* third growth (262,144 -> 524,288 nodes): the arrays grow by about 12 MiB, the table needs 2 MiB */
  long v2 = vm_bytes();
  cap(12L << 20 | 512L << 10);
  bool ok3 = make_until((1L << 18) + 64);
  uncap();
  printf("    third capped growth: address space %+ld KiB (%s)\n", (vm_bytes() - v2) >> 10, ok3 ? "went on" : "refused");
  printf("    term making across the first two capped growths: %s, %s\n", ok1 ? "went on" : "refused", ok2 ? "went on" : "refused");
  int sig = kc_survives(fill_past_capacity);
  HOLDS(sig == 0, "after failed growths, making terms still terminates (no endless probing of a full table)");
  if (sig) printf("    child stopped with signal/status %d (14 = alarm: endless probing)\n", sig);
  FINISH("k31_hash_growth_failure");
}
