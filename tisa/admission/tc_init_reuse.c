/* tc_init_reuse.c: tc_init keeps its tables and clears what the previous state wrote. Built with
   -DTC_INIT_VERIFY, every tc_init after the first checks that each kept table is all zero over its
   whole allocation and aborts otherwise; each scene below writes through one extent tc_init must
   clear, then calls tc_init. Prints "holds" per scene; exit 0 when every scene ran. */
#include "../../tcalc.h"
#include <stdio.h>

static int scenes;
#define HOLDS(c, what) do { if (c) { printf("  holds     %s\n", what); scenes++; } else { printf("  NO SCENE  %s\n", what); return 2; } } while (0)

static int s_w, s_f, c_pair;
static bool theory(uint32_t nodes, uint32_t occs) {
    if (!tc_init(nodes, occs)) return false;
    s_f = tc_sort(SORT_PROVABLE); s_w = tc_sort(0);
    Binder b[2] = { { (uint16_t)s_w, 0, 0 }, { (uint16_t)s_w, 0, 0 } };
    c_pair = tc_con((uint16_t)s_f, 0, 2, b);
    return s_f > 0 && s_w > 0 && c_pair >= 0;
}
static Term lit(uint64_t v) { return tc_name((uint16_t)s_w, (1ull << 62) | v); }
static Term pair(uint64_t x, uint64_t y) { Term a[2] = { lit(x), lit(y) }; return tc_app(c_pair, a); }

int main(void) {
    printf("tc_init keeps its tables\n");
    /* the node and argument arenas grow past their capacity, names and the posted-term index are made */
    bool ok = theory(256, 64);
    for (uint64_t i = 0; ok && i < 3000; i++) ok = pair(i, i + 1) != 0;
    ok = ok && tc_post(1, pair(1, 2)) != 0 && tc_post_at(tc_space_term(9), pair(3, 4), false) != 0;
    HOLDS(ok, "3000 terms past a 256-node arena, names, a post and a located post");
    HOLDS(theory(256, 64), "tc_init clears them (grown arenas, name and index tables kept as spares)");
    /* a birth scope: a rule installed in it keeps its patterns and rolls the other new nodes back */
    Binder v[2] = { { (uint16_t)s_w, 0, 0 }, { (uint16_t)s_w, 0, 0 } };
    ok = tc_ctx(2, v);
    tc_birth();
    for (uint64_t i = 0; ok && i < 500; i++) ok = pair(i + 10000, i) != 0;   /* made in the scope, dropped by its release */
    Rule r = { 0 };
    r.fresh = -1; r.nkeep = 1;
    Term k[2] = { tc_v(0), tc_v(1) }, m[2] = { tc_v(1), tc_v(0) };
    r.keep[0] = (Pat){ tc_app(c_pair, k), 3 }; r.make = (Pat){ tc_app(c_pair, m), 3 };
    HOLDS(ok && tc_rule(&r) >= 0, "a rule installed in a birth scope rolls back the 1500 nodes made in it");
    HOLDS(theory(256, 64), "tc_init clears what the rolled-back nodes wrote");
    /* the board grows past its capacity by posts, then in slot mode, where growth fills new slots above
       the board while posts append one by one */
    ok = true;
    for (uint64_t i = 0; ok && i < 200; i++) ok = tc_post(0, pair(i, 7)) != 0;
    HOLDS(ok, "200 posts past a 64-occurrence board");
    HOLDS(theory(256, 4), "tc_init clears the grown board");
    Occ u = tc_post(0, pair(1, 2));
    if (u) tc_unset(u);
    HOLDS(u && tc_post(0, pair(3, 4)) != 0, "slot mode, then a post past the capacity: the new slots are filled above the board");
    HOLDS(theory(256, 4), "tc_init clears the slots written above the board");
    /* sizes change between runs: a large board, a small one, a large one again */
    ok = theory(1u << 16, 1u << 12);
    for (uint64_t i = 0; ok && i < 5000; i++) ok = tc_post(2, pair(i, i)) != 0;
    HOLDS(ok, "a large run");
    ok = theory(256, 8) && tc_post(2, pair(5, 5)) != 0;
    HOLDS(ok, "a small run reuses the large tables");
    HOLDS(theory(1u << 16, 1u << 12), "a large run again: every table clear");
    printf("tc_init_reuse: holds (%d scenes)\n", scenes);
    return 0;
}
