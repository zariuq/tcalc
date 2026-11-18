/* ABS plan execution against the binding walk's independent C models. */
#define main bind_walk_fixture_generator_main
#include "../walks/bind_walk_tests.c"
#undef main
#include "native_abi.h"
#include "cet_profile.h"
#include <stddef.h>

typedef struct {
    const uint64_t *plan, *plan_end;
    uint64_t *ctl;
    const uint64_t *bind, *leaves;
    uint64_t budget, used;
    const uint64_t *at;
} AbsDrive;
_Static_assert(sizeof(AbsDrive) == TISA_ABI_DriveWords * TISA_ABI_WordBytes, "drive size");
_Static_assert(offsetof(AbsDrive, used) == TISA_ABI_DriveDescriptor_used_OFFSET, "receipt");
extern uint64_t tisa_drive(AbsDrive *);
extern const uint8_t abs_intern16[], abs_pack[], abs_eqw[], abs_row_word[];
extern const uint8_t abs_live[], abs_append_row[], abs_bind_walk[];

enum { ABS_TERM_CAP = 128, ABS_CONTROL = 40, ABS_STEPS = 16, ABS_GUARD_STEPS = 4 };
typedef struct {
    uint64_t first_guard;
    Store ty, db;
    uint64_t term[ABS_TERM_CAP][5], count, marks[ABS_TERM_CAP];
    uint64_t last_guard;
} AbsKernel;

static void abs_initial(AbsKernel *s, unsigned trial) {
    memset(s, 0, sizeof *s);
    s->first_guard = s->last_guard = UINT64_C(0xACED37AB51C0FFEE);
    store_init(&s->ty, MAXR0, MAXR1, 8, MAXR3);
    store_init(&s->db, MAXR0, MAXR1, 8, MAXR3);
    uint64_t ty[][2] = {{2,0},{1,0},{24,0},{11,0}};
    for (unsigned j = 0; j < 4; ++j)
        if (intern_pub(&s->ty, ty[j][0], ty[j][1]) != j) die("type fixture");
    if (intern_pub(&s->db, 5, 0) != 0 || intern_pub(&s->db, 32, 1) != 1 ||
        intern_pub(&s->db, 40, 1) != 2) die("term fixture");
    const uint64_t terms[][5] = {{0,4,1,1,1},{0,5,1,1,2}};
    memcpy(s->term, terms, sizeof terms);
    s->count = 2;
    for (unsigned j = 0; j < MAXR3; ++j) s->db.b3[j] = (uint8_t)(trial ? next() : 0xA5);
}

static void abs_plan(uint64_t plan[ABS_STEPS * 18]) {
    static const uint64_t fields[ABS_STEPS][9] = {
        /* leaf, arg0, arg1, v1..v5, payload */
        {5,8,0,0,0,0,0,0,24}, {5,9,0,0,0,0,0,0,25},
        {4,8,0,5,0,0,0,0,26}, {3,26,0,0,0,0,0,0,27},
        {4,8,1,5,0,0,0,0,28}, {4,8,3,5,0,0,0,0,29},
        {4,9,3,5,0,0,0,0,30}, {4,9,4,5,0,0,0,0,31},
        {10,28,29,31,0,0,0,0,32},
        {1,30,3,0,0,0,0,0,33}, {0,33,0,0,0,0,0,0,34},
        {1,29,3,0,0,0,0,0,35}, {0,35,34,0,0,0,0,0,36},
        {1,1,1,0,0,0,0,0,37}, {0,37,36,0,0,0,0,0,38},
        {6,3,8,5,9,38,32,0,39}
    };
    for (unsigned i = 0; i < ABS_STEPS; ++i) {
        uint64_t *st = plan + 18 * i;
        st[0] = fields[i][0];
        for (unsigned j = 1; j <= 9; ++j) st[j] = 56;
        for (unsigned j = 0; j < 8; ++j) st[10+j] = fields[i][1+j];
        if (i == 0 || i == 1) { st[1] = 14; st[2] = 16; }
        else if (i == 2 || (i >= 4 && i <= 7) || i == 15) { st[1] = 12; st[2] = 14; }
        else if (i == 8) { st[1] = 6; st[2] = 8; st[3] = 10; st[4] = 42; }
        else if (i == 10 || i == 12 || i == 14) { st[1] = 0; st[2] = 2; st[3] = 4; }
    }
#ifdef ABS_MUTATION
    if (ABS_MUTATION == 1) plan[3*18+10] = 0;
    if (ABS_MUTATION == 2) plan[8*18+12] = 29;
    if (ABS_MUTATION == 3) plan[9*18+11] = 2;
    if (ABS_MUTATION == 4) plan[15*18+14] = 32;
    if (ABS_MUTATION == 5) {
        uint64_t tmp[18]; memcpy(tmp,plan+15*18,sizeof tmp);
        memcpy(plan+15*18,plan+8*18,sizeof tmp); memcpy(plan+8*18,tmp,sizeof tmp);
    }
    if (ABS_MUTATION == 6) plan[8*18+4] = 40;
    if (ABS_MUTATION == 7) plan[6*18+2] = 10;
#endif
}

static void abs_bindings(AbsKernel *s, uint64_t bindings[58]) {
    memset(bindings, 0, 58 * sizeof *bindings);
    bindings[0] = (uint64_t)(uintptr_t)s->ty.b0; bindings[1] = s->ty.len[0];
    bindings[2] = (uint64_t)(uintptr_t)s->ty.b1; bindings[3] = s->ty.len[1];
    bindings[4] = (uint64_t)(uintptr_t)s->ty.b2; bindings[5] = s->ty.len[2];
    bindings[6] = (uint64_t)(uintptr_t)s->db.b0; bindings[7] = s->db.len[0];
    bindings[8] = (uint64_t)(uintptr_t)s->db.b1; bindings[9] = s->db.len[1];
    bindings[10] = (uint64_t)(uintptr_t)s->db.b2; bindings[11] = s->db.len[2];
    bindings[12] = (uint64_t)(uintptr_t)s->term; bindings[13] = sizeof s->term;
    bindings[14] = (uint64_t)(uintptr_t)&s->count; bindings[15] = 8;
    bindings[16] = (uint64_t)(uintptr_t)s->marks; bindings[17] = sizeof s->marks;
    bindings[42] = (uint64_t)(uintptr_t)s->db.b3; bindings[43] = s->db.len[3];
}

static unsigned abs_model(AbsKernel *s, uint64_t v, uint64_t t, uint64_t *at, uint64_t *image) {
    if (v >= s->count || s->marks[v]) { *at = 0; return 0; }
    if (t >= s->count || s->marks[t]) { *at = 1; return 0; }
    if (s->term[v][0] != 0) { *at = 3; return 0; }
    *at = 8;
    static Store walk_before;
    walk_before = s->db;
    Result r = walk_model(&s->db, s->term[v][1], s->term[v][3], s->term[t][4]);
    check_spec(&walk_before,&s->db,r,s->term[v][1],s->term[v][3],s->term[t][4],"ABS plan");
    if (r.out != FIRED) return (unsigned)r.out;
    *image = r.ret;
    uint64_t tail = intern_pub(&s->ty, 3 + 8 * s->term[t][3], 0);
    *at = 10; if (tail == UINT64_MAX) return 2;
    uint64_t args = intern_pub(&s->ty, 3 + 8 * s->term[v][3], tail);
    *at = 12; if (args == UINT64_MAX) return 2;
    uint64_t funty = intern_pub(&s->ty, 9, args);
    *at = 14; if (funty == UINT64_MAX) return 2;
    *at = 15;
    if (s->count == ABS_TERM_CAP) return 2;
    uint64_t row[] = {3,v,t,funty,r.ret};
    memcpy(s->term[s->count++], row, sizeof row);
    *at = ABS_STEPS;
    return 1;
}

static void abs_rows_check(const AbsKernel *s) {
    uint64_t n = rd(&s->db, 2, 0);
    if (!intern_ok(&s->db, n) || !intern_ok(&s->ty, rd(&s->ty, 2, 0))) die("ABS interner invariant");
    decode_reset(n);
    for (uint64_t i = 0; i < n; ++i) {
        uint64_t k0 = rd(&s->db, 0, 16*i), b = rd(&s->db, 0, 16*i+8);
        uint64_t tag = k0 & 7, a = k0 >> 3;
        if ((tag == 1 && b) || (tag == 3 && (a >= i || b >= i)) ||
            (tag == 4 && b >= i) || (tag == 5 && (a || b)) ||
            (tag != 5 && !decode(&s->db, n, i))) die("ABS row construction invariant");
    }
}

static uint64_t abs_cases;
static void abs_guard_case(AbsKernel *s, uint64_t binder, uint64_t body,
                           bool admit, unsigned stop) {
    static AbsKernel before;
    before = *s;
    uint64_t plan[ABS_STEPS * 18], bind[58], ctl[ABS_CONTROL] = {0};
    abs_plan(plan);
    abs_bindings(s, bind);
#ifdef ABS_GUARD_MUTATION
    /* Replace exactly one semantic check by equality of zero with zero. */
    unsigned replace = ABS_GUARD_MUTATION == 3 ? 3 : ABS_GUARD_MUTATION - 1;
    uint64_t replacement[18] = {
        3,56,56,56,56,56,56,56,56,56,0,0,0,0,0,0,0,24 + replace
    };
    memcpy(plan + 18 * replace, replacement, sizeof replacement);
#endif
    for (unsigned j = 0; j <= 6; ++j) ctl[j] = j;
    ctl[7] = 2;
    ctl[8] = binder;
    ctl[9] = body;
    uint64_t original[24];
    memcpy(original, ctl, sizeof original);
    uint64_t eqpc = (uint64_t)(uintptr_t)abs_eqw;
    uint64_t leaves[] = {eqpc, eqpc, eqpc, eqpc, (uint64_t)(uintptr_t)abs_row_word,
                         (uint64_t)(uintptr_t)abs_live};
    AbsDrive d = {plan, plan + ABS_GUARD_STEPS * 18, ctl, bind, leaves, 0, 0, NULL};
    uint64_t result = tisa_drive(&d);
    if (result != (admit ? 1u : 0u) || d.at != plan + 18 * stop || d.used ||
        memcmp(original, ctl, sizeof original) || memcmp(&before, s, sizeof before)) {
        fprintf(stderr, "ABS guard v=%" PRIu64 " t=%" PRIu64 " outcome=%" PRIu64
                        " expected=%u or frame/receipt mismatch\n",
                binder, body, result, admit ? 1u : 0u);
        exit(1);
    }
}

static void abs_guard_tests(AbsKernel *s) {
    abs_initial(s, 0);
    abs_guard_case(s, 0, 1, true, ABS_GUARD_STEPS);
    abs_guard_case(s, 0, 0, true, ABS_GUARD_STEPS);
    s->marks[0] = 1;
    abs_guard_case(s, 0, 1, false, 0);
    abs_guard_case(s, 1, 0, false, 1);
    s->marks[0] = 0;
    abs_guard_case(s, s->count, 1, false, 0);
    abs_guard_case(s, 1, s->count, false, 1);
    uint64_t at, image;
    if (abs_model(s, 0, 0, &at, &image) != 1) die("ABS guard fixture");
    abs_guard_case(s, 2, 1, false, 3);
    puts("ABS admission prefix: 7 runs, 0 differences; frame and receipt checks passed");
}

static void abs_compare(AbsKernel *s, uint64_t v, uint64_t t, unsigned budget_bad) {
    static AbsKernel expected;
    expected = *s;
    uint64_t want_at = 0, image = UINT64_MAX;
    unsigned want = budget_bad ? 3 : abs_model(&expected, v, t, &want_at, &image);
    uint64_t plan[ABS_STEPS * 18], bind[58], controls[ABS_CONTROL + 2];
    abs_plan(plan); abs_bindings(s, bind);
    uint64_t *ctl = controls + 1;
    for (unsigned j = 0; j < ABS_CONTROL + 2; ++j) controls[j] = UINT64_C(0x5A5AC0FFEE00BEEF);
    for (unsigned j = 0; j <= 6; ++j) ctl[j] = j;
    ctl[7] = 2; ctl[8] = v; ctl[9] = t; ctl[22] = UINT64_C(14695981039346656037);
    uint64_t original[24]; memcpy(original, ctl, sizeof original);
    uint64_t leaves[11] = {(uint64_t)(uintptr_t)abs_intern16, (uint64_t)(uintptr_t)abs_pack,
        0, (uint64_t)(uintptr_t)abs_eqw, (uint64_t)(uintptr_t)abs_row_word,
        (uint64_t)(uintptr_t)abs_live, (uint64_t)(uintptr_t)abs_append_row,
        0,0,0,(uint64_t)(uintptr_t)abs_bind_walk};
    AbsDrive d = {plan, plan + ABS_STEPS * 18, ctl, bind, leaves, 0, budget_bad ? 1 : 0, 0};
    uint64_t got = tisa_drive(&d);
    if (got != want || d.at != plan + 18 * want_at || d.used != (budget_bad ? 1u : 0u) ||
        memcmp(&expected, s, sizeof *s) || memcmp(original, ctl, sizeof original) ||
        controls[0] != UINT64_C(0x5A5AC0FFEE00BEEF) ||
        controls[ABS_CONTROL+1] != UINT64_C(0x5A5AC0FFEE00BEEF) ||
        (got == 1 && ctl[32] != image)) {
        fprintf(stderr, "ABS case %" PRIu64 " v=%" PRIu64 " t=%" PRIu64
            " outcome=%" PRIu64 "/%u step=%td/%" PRIu64 " bytes=%d\n",
            abs_cases,v,t,got,want,(d.at-plan)/18,want_at,memcmp(&expected,s,sizeof *s));
        exit(1);
    }
    abs_rows_check(s);
    ++abs_cases;
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1],"--dump-plan")) {
        uint64_t plan[ABS_STEPS*18]; abs_plan(plan);
        for (unsigned j = 0; j < ABS_STEPS*18; ++j)
            printf("%" PRIu64 "%c",plan[j],j%18 == 17 ? '\n' : ' ');
        return 0;
    }
    if (!cet_profile()) return 2;
    static AbsKernel s;
    trees_reset();
    if (argc == 2 && !strcmp(argv[1],"--guard-only")) {
        abs_guard_tests(&s);
        return 0;
    }
    for (unsigned trial = 0; trial < 24; ++trial) {
        abs_initial(&s, trial);
        abs_compare(&s,0,0,0); abs_compare(&s,0,1,0); abs_compare(&s,1,0,0);
        for (unsigned j = 0; j < 8; ++j) abs_compare(&s,0,0,0);
        for (unsigned j = 0; j < 20; ++j) abs_compare(&s,j%2,s.count-1,0);
        abs_compare(&s,2,0,0); abs_compare(&s,s.count,0,0); abs_compare(&s,0,s.count,0);
        s.marks[0] = 1; abs_compare(&s,0,1,0); abs_compare(&s,1,0,0); s.marks[0] = 0;
        abs_compare(&s,0,1,1);
        abs_initial(&s, trial); s.ty.len[0] = 16*4; abs_compare(&s,0,0,0);
        abs_initial(&s, trial); s.db.len[0] = 16*3; abs_compare(&s,0,0,0);
        abs_initial(&s, trial); s.db.len[3] = 256; abs_compare(&s,0,0,0);
        abs_initial(&s, trial);
        for (unsigned j = 2; j < ABS_TERM_CAP; ++j) memcpy(s.term[j],s.term[0],sizeof s.term[0]);
        s.count = ABS_TERM_CAP; abs_compare(&s,0,1,0);
    }
    printf("ABS native plan: %" PRIu64 " runs, 0 differences; row, frame and receipt checks passed\n",abs_cases);
    return 0;
}
