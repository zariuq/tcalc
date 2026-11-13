/* k25: a refused firing leaves the store as it was, also when the refusal comes late.
   In a sealed store without takes or counts, post() answers a make whose fact is already present
   with the existing occurrence. If a later make of the same firing cannot be stored (here: the
   board cannot grow because the address space is capped), the rollback marks every occurrence the
   firing "made" dead, including that pre-existing one: a fact disappears without being taken.
   Repository build only (the address-space cap is incompatible with the sanitizers). */
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

int main(void) {
  SETUP(tc_init(1u << 18, 1u << 16));
  NAT = tc_sort(0); THM = tc_sort(SORT_PROVABLE);
  Binder n1 = { (uint16_t)NAT, 0, 0 };
  A1c = tc_con((uint16_t)THM, 0, 1, &n1); B1c = tc_con((uint16_t)THM, 0, 1, &n1); W1c = tc_con((uint16_t)THM, 0, 1, &n1);
  SETUP(A1c >= 0 && B1c >= 0 && W1c >= 0);
  kc_ctx_nat(1);
  Rule two = { .nkeep = 1, .keep = { { kc_u(A1c, tc_v(0)), 1 } }, .make = { kc_u(B1c, tc_v(0)), 1 },
               .nmake_extra = 1, .make_extra = { { kc_u(W1c, tc_v(0)), 1 } }, .fresh = -1 };   /* A1(x) |- B1(x), W1(x) */
  int r = tc_rule(&two);
  SETUP(r >= 0);
  for (int i = 0; i < 70000; i++) (void)tc_fresh_name();
  Term n0 = tc_name((uint16_t)NAT, 0);
  Occ oa = tc_post(1, kc_u(A1c, n0)), ob = tc_post(1, kc_u(B1c, n0));    /* B1(n0) is already there */
  SETUP(oa && ob);
  tc_protect(1); tc_seal();
  /* fill the board to its capacity with distinct facts in unprotected space 0 */
  Occ last = 0;
  for (uint64_t i = 1; last < (1u << 16) - 1 && i < 70000; i++) { Occ o = tc_post(0, kc_u(A1c, tc_name((uint16_t)NAT, i))); if (!o) break; last = o; }
  SETUP(last == (1u << 16) - 1);                         /* the last slot of the board is used */
  long vm = vm_bytes();
  SETUP(vm > 0);
  struct rlimit rl = { (rlim_t)(vm + (1 << 20)), (rlim_t)(vm + (1 << 20)) };
  SETUP(setrlimit(RLIMIT_AS, &rl) == 0);                 /* the next board doubling cannot be allocated */
  Occ w = tc_fire(r, NULL, &oa, NULL);
  printf("    firing %s (the extra make W1(n0) %s)\n", w ? "admitted" : "refused", w ? "was stored" : "could not be stored");
  HOLDS(tc_alive(ob) && tc_term(ob) == kc_u(B1c, n0), "B1(n0), present before the firing, is still in protected space 1");
  FINISH("k25_rollback_set_store");
}
