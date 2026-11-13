/* test_ref.c: controls for tcalc_ref.  Every control states its expected outcome; a control
 * transcribed from the Lean development carries the theorem's name. */
#include "tcalc_ref.h"

#include <stdlib.h>
#include <string.h>

static int passed, failed;
#define CHECK(cond, name)                                                  \
  do {                                                                     \
    if (cond) passed++;                                                    \
    else { failed++; fprintf(stderr, "FAIL %s (line %d)\n", name, __LINE__); } \
  } while (0)

/* ---- a firing builder for tests (fixed capacities are a test convenience, checked) ---- */
#define CAP 256
typedef struct {
  tr_ctx *c;
  tr_scope *sc;
  tr_use takes[CAP], reads[CAP];
  tr_make makes[CAP];
  tr_eq tells[CAP], apart[CAP];
  tr_guard guards[CAP];
  tr_firing f;
} fb;

static void fb_init(fb *b, tr_ctx *c) {
  memset(b, 0, sizeof *b);
  b->c = c;
  b->sc = tr_scope_new();
  b->f.takes = b->takes;
  b->f.reads = b->reads;
  b->f.makes = b->makes;
  b->f.tells = b->tells;
  b->f.apart = b->apart;
  b->f.guards = b->guards;
}
static void fb_free(fb *b) { tr_scope_free(b->sc); }
static tr_term T(fb *b, const char *text) {
  tr_term t = tr_read(b->c, b->sc, text);
  if (t == TR_NONE) { fprintf(stderr, "bad term %s\n", text); exit(2); }
  return t;
}
static const tr_firing *F(fb *b) {
  if (b->f.ntakes > CAP || b->f.nreads > CAP || b->f.nmakes > CAP || b->f.ntells > CAP ||
      b->f.napart > CAP || b->f.nguards > CAP) { fprintf(stderr, "test builder full\n"); exit(2); }
  b->f.locals = tr_scope_size(b->sc);
  return &b->f;
}
static void take(fb *b, const char *p, tr_occ o) { b->takes[b->f.ntakes++] = (tr_use){T(b, p), o}; }
static void readp(fb *b, const char *p, tr_occ o) { b->reads[b->f.nreads++] = (tr_use){T(b, p), o}; }
static void make(fb *b, const char *l) { b->makes[b->f.nmakes++] = (tr_make){T(b, l), 0, 0}; }
static void make_id(fb *b, const char *l, tr_occ id) { b->makes[b->f.nmakes++] = (tr_make){T(b, l), id, 0}; }
static void make_schema(fb *b, const char *l, uint32_t n) {
  /* a stored schema: its locals are its own, read in a scope of its own */
  tr_scope *own = tr_scope_new();
  tr_term t = tr_read(b->c, own, l);
  tr_scope_free(own);
  b->makes[b->f.nmakes++] = (tr_make){t, 0, n};
}
static void tell(fb *b, const char *l, const char *r) { b->tells[b->f.ntells++] = (tr_eq){T(b, l), T(b, r)}; }
static void apart(fb *b, const char *l, const char *r) { b->apart[b->f.napart++] = (tr_eq){T(b, l), T(b, r)}; }
static void guard(fb *b, tr_guard g) { b->guards[b->f.nguards++] = g; }
static void absent(fb *b, const char *p) { guard(b, (tr_guard){.kind = TR_G_ABSENT, .a = T(b, p)}); }
static void count(fb *b, const char *p, size_t n) { guard(b, (tr_guard){.kind = TR_G_COUNT, .a = T(b, p), .number = n}); }
static void ask(fb *b, const char *l, const char *r) { guard(b, (tr_guard){.kind = TR_G_EQUAL, .a = T(b, l), .b = T(b, r)}); }

/* One firing written in one line: "take p(X)@3; read q@4; make r(X); tell X=a; apart X=b;
 * absent s(X); count t(X)=2; ask X=a; mint 1". */
static tr_verdict run1(tr_state *s, const char *text, bool commit, tr_result *res) {
  fb b;
  fb_init(&b, tr_state_ctx(s));
  char *copy = strdup(text), *save = NULL;
  for (char *part = strtok_r(copy, ";", &save); part; part = strtok_r(NULL, ";", &save)) {
    while (*part == ' ') part++;
    char *arg = strchr(part, ' ');
    if (!arg) continue;
    *arg++ = 0;
    char *at = strrchr(arg, '@'), *eq = strchr(arg, '=');
    if (!strcmp(part, "take") || !strcmp(part, "read")) {
      /* the occurrence follows the last '@' that is followed by digits only up to the end */
      *at = 0;
      (part[0] == 't' ? take : readp)(&b, arg, strtoull(at + 1, NULL, 10));
    } else if (!strcmp(part, "make")) {
      if (at && at > arg && at[-1] == ' ') { *at = 0; make_id(&b, arg, strtoull(at + 1, NULL, 10)); }
      else make(&b, arg);
    } else if (!strcmp(part, "tell") || !strcmp(part, "apart") || !strcmp(part, "ask")) {
      *eq = 0;
      (part[1] == 'e' ? tell : part[1] == 'p' ? apart : ask)(&b, arg, eq + 1);
    } else if (!strcmp(part, "absent")) {
      absent(&b, arg);
    } else if (!strcmp(part, "count")) {
      *eq = 0;
      count(&b, arg, strtoull(eq + 1, NULL, 10));
    } else if (!strcmp(part, "mint")) {
      b.f.fresh = (uint32_t)strtoul(arg, NULL, 10);
    } else {
      fprintf(stderr, "bad part %s\n", part);
      exit(2);
    }
  }
  tr_result scratch = {0};
  if (!res) res = &scratch;
  tr_verdict v = commit ? tr_fire(s, F(&b), res) : tr_admits(s, F(&b), res);
  free(copy);
  fb_free(&b);
  return v;
}
static bool fires(tr_state *s, const char *text) { return run1(s, text, true, NULL) == TR_ADMITTED; }
static bool admits(tr_state *s, const char *text) { return run1(s, text, false, NULL) == TR_ADMITTED; }
static tr_reason why(tr_state *s, const char *text) {
  tr_result r = {0};
  run1(s, text, false, &r);
  return r.reason;
}

/* Present labels as a sorted text, for comparing stores as bags. */
static int cmpstr(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }
static char *bag(const tr_state *s) {
  size_t n = tr_present_count(s);
  char **items = calloc(n + 1, sizeof *items);
  size_t total = 1;
  tr_occ o = 0;
  for (size_t i = 0; i < n; i++) {
    tr_term l;
    o = tr_next_present(s, o, &l);
    char *buf = NULL;
    size_t len = 0;
    FILE *m = open_memstream(&buf, &len);
    tr_print(m, tr_state_ctx(s), l);
    fclose(m);
    items[i] = buf;
    total += len + 1;
  }
  qsort(items, n, sizeof *items, cmpstr);
  char *out = calloc(total, 1);
  for (size_t i = 0; i < n; i++) {
    if (i) strcat(out, " ");
    strcat(out, items[i]);
    free(items[i]);
  }
  free(items);
  return out;
}
static bool bag_is(const tr_state *s, const char *expect) {
  char *b = bag(s);
  bool ok = strcmp(b, expect) == 0;
  if (!ok) fprintf(stderr, "  bag [%s] expected [%s]\n", b, expect);
  free(b);
  return ok;
}

/* A state holding the occurrences ids[i] labelled labels[i] (made by one firing). */
static tr_state *store(tr_ctx *c, size_t n, const tr_occ *ids, const char *const *labels) {
  tr_state *s = tr_state_new(c);
  fb b;
  fb_init(&b, c);
  for (size_t i = 0; i < n; i++) make_id(&b, labels[i], ids[i]);
  if (tr_fire(s, F(&b), NULL) != TR_ADMITTED) { fprintf(stderr, "store setup failed\n"); exit(2); }
  fb_free(&b);
  return s;
}
/* Occurrences labelled by their own identity (the controls' `id` labelling). */
static tr_state *idstore(tr_ctx *c, size_t n, const tr_occ *ids) {
  const char **labels = calloc(n + 1, sizeof *labels);
  char (*text)[24] = calloc(n + 1, sizeof *text);
  for (size_t i = 0; i < n; i++) { snprintf(text[i], 24, "%llu", (unsigned long long)ids[i]); labels[i] = text[i]; }
  tr_state *s = store(c, n, ids, labels);
  free(labels);
  free(text);
  return s;
}
/* A firing that declares n unknowns: variables first .. first+n-1. */
static uint32_t declare(tr_state *s, uint32_t n) {
  fb b;
  fb_init(&b, tr_state_ctx(s));
  for (uint32_t i = 0; i < n; i++) { char v[32]; snprintf(v, sizeof v, "V%u", i); T(&b, v); }
  tr_term *locals = calloc(n + 1, sizeof *locals);
  tr_result r = {.locals = locals};
  tr_fire(s, F(&b), &r);
  fb_free(&b);
  uint32_t first = tr_term_index(tr_state_ctx(s), locals[0]); /* left unbound: new variables, in order */
  for (uint32_t i = 0; i < n; i++)
    if (tr_term_kind(tr_state_ctx(s), locals[i]) != TR_VAR || tr_term_index(tr_state_ctx(s), locals[i]) != first + i) {
      fprintf(stderr, "declare: unexpected variables\n");
      exit(2);
    }
  free(locals);
  return first;
}

/* ============================================================================================ */

static void lean_tensor_controls(tr_ctx *c) {
  /* KnowledgeTensorFirstOrderControls: labels are the identities themselves. */
  tr_state *one = idstore(c, 1, (tr_occ[]){5});
  tr_state *withNine = idstore(c, 2, (tr_occ[]){5, 9});
  CHECK(admits(one, "read 5@5; read 5@5; make 7 @7"), "pick_is_admitted (two reads of one occurrence)");
  {
    tr_state *s = tr_state_clone(one);
    fires(s, "read 5@5; read 5@5; make 7 @7");
    CHECK(bag_is(s, "5 7"), "the_use_reads_one_copy (the read occurrence stays, once)");
    tr_state_free(s);
  }
  CHECK(!admits(one, "take 5@5; take 5@5; make 7"), "one_copy_for_each_take: a take list with one occurrence twice is refused");
  CHECK(admits(one, "read 5@5") && admits(one, "take 5@5"), "OccurrenceCommits.Controls.reader_enabled, taker_enabled");
  CHECK(why(one, "read 5@0") == TR_FITS && why(one, "take 5@0") == TR_SHAPES && !tr_present(one, 0, NULL),
        "identity 0 names nothing (read: not present; take: not a take)");
  {
    tr_guard q = {.kind = TR_G_QUERY, .seen = (tr_occ[]){0}, .nseen = 1};
    extern tr_member everything(tr_view *, tr_term, void *);
    q.region = everything;
    tr_state *e = tr_state_new(c);
    tr_firing f = {.guards = &q, .nguards = 1};
    tr_guard q2 = {.kind = TR_G_QUERY, .region = everything};
    tr_firing f2 = {.guards = &q2, .nguards = 1};
    CHECK(tr_admits(e, &f, NULL) == TR_REFUSED && tr_admits(e, &f2, NULL) == TR_ADMITTED,
          "a query that saw identity 0 never holds; the empty region with nothing seen holds");
    tr_state_free(e);
  }
  CHECK(!admits(one, "take 5@5; read 5@5") && why(one, "take 5@5; read 5@5") == TR_FITS,
        "OccurrenceCommits.Controls.read_take_same_not_enabled (Enabled.apart)");
  CHECK(admits(one, "absent 9; make 7 @7"), "unless_nine_is_admitted");
  CHECK(!admits(withNine, "absent 9; make 7 @7"), "unless_nine_is_refused_beside_nine");
  {
    tr_state *s = store(c, 1, (tr_occ[]){1}, (const char *[]){"0"});
    tr_state *t = store(c, 1, (tr_occ[]){2}, (const char *[]){"0"});
    tr_guard q = {.kind = TR_G_QUERY, .seen = (tr_occ[]){1}, .nseen = 1};
    extern tr_member everything(tr_view *, tr_term, void *);
    q.region = everything;
    tr_firing f = {.guards = &q, .nguards = 1};
    CHECK(tr_admits(s, &f, NULL) == TR_ADMITTED && tr_admits(t, &f, NULL) == TR_REFUSED,
          "a_predicate_query_observes_identities (same labels, different identities)");
    tr_state_free(s);
    tr_state_free(t);
  }
  CHECK(!admits(one, "tell 1=2") && why(one, "tell 1=2") == TR_UNSOLVABLE, "and_it_has_no_admitted_firing (tell 1 = 2)");
  {
    /* KnowledgeTensorCoreControls: every occurrence labelled 5. */
    for (size_t n = 0; n <= 4; n++)
      for (size_t number = 0; number <= 5; number++) {
        tr_occ ids[4] = {10, 11, 12, 13};
        const char *labels[4] = {"5", "5", "5", "5"};
        tr_state *s = store(c, n, ids, labels);
        char text[32];
        snprintf(text, sizeof text, "count 5=%zu", number);
        CHECK(admits(s, text) == (n == number), "counts_valid_iff (present.card = number)");
        tr_state_free(s);
      }
    tr_state *zero = store(c, 1, (tr_occ[]){0 + 100}, (const char *[]){"5"});
    tr_state *both = store(c, 2, (tr_occ[]){100, 101}, (const char *[]){"5", "5"});
    tr_state *another = store(c, 1, (tr_occ[]){101}, (const char *[]){"5"});
    CHECK(admits(zero, "count 5=1"), "counts_one_admitted");
    CHECK(!admits(both, "count 5=1"), "counts_one_refused_beside_another");
    CHECK(why(both, "count 5=1") == TR_GUARD, "counts_one_prepared_beside_another (prepared; only the guard fails)");
    CHECK(admits(both, "count 5=2") && !admits(zero, "count 5=2") && !admits(another, "count 5=2"),
          "a_count_is_enabled_by_its_context (a count satisfied only in company)");
    tr_state *occupied = idstore(c, 2, (tr_occ[]){5, 7});
    CHECK(why(occupied, "read 5@5; read 5@5; make 7 @7") == TR_FITS, "nothing_fits_beside_an_occupied_output");
    tr_state_free(zero);
    tr_state_free(both);
    tr_state_free(another);
    tr_state_free(occupied);
  }
  {
    /* KnowledgeTensorCoreTraceControls.interchange_fails_for_counting: labels all 5. */
    const char *adds = "make 5 @7", *removes = "take 5@7", *counts1 = "count 5=1";
    tr_state *a = store(c, 1, (tr_occ[]){100}, (const char *[]){"5"}), *b = tr_state_clone(a), *m = tr_state_clone(a);
    bool cut = fires(a, adds) && fires(a, removes) && fires(a, counts1);
    bool tensor = fires(b, counts1) && fires(b, adds) && fires(b, removes);
    bool between = fires(m, adds) && !admits(m, counts1);
    CHECK(cut && tensor && between, "interchange_fails_for_counting (both orders run; between adds and removes the count is two)");
    tr_state_free(a); tr_state_free(b); tr_state_free(m);
    /* KnowledgeTensorCoreWeightInterchangeControls.interchange_fails_for_absence */
    const char *unlessFive = "absent 5";
    tr_state *e = tr_state_new(c), *g = tr_state_new(c), *h = tr_state_new(c);
    CHECK(!admits(e, removes), "removes_not_first_bare");
    bool cutA = fires(e, adds) && fires(e, removes) && fires(e, unlessFive);
    bool tensorA = fires(g, unlessFive) && fires(g, adds) && fires(g, removes);
    bool betweenA = fires(h, adds) && !admits(h, unlessFive);
    CHECK(cutA && tensorA && betweenA, "interchange_fails_for_absence (unlessFive_not_between)");
    tr_state_free(e); tr_state_free(g); tr_state_free(h);
  }
  {
    /* KnowledgeTensorCoreWeightChanceControls / SeparatedControls, exhaustively over S. */
    int okFive = 1, okSix = 1, okCounts = 1;
    for (unsigned S = 0; S < 1024; S++) {
      tr_occ ids[12];
      size_t n = 0;
      ids[n++] = 5;
      for (unsigned a = 0; a < 10; a++) if ((S >> a & 1) && a != 5) ids[n++] = a;
      tr_state *s = idstore(c, n, ids);
      bool disjoint79 = !(S >> 7 & 1) && !(S >> 9 & 1);
      okFive &= admits(s, "absent 9; make 7 @7") == disjoint79;
      tr_state_free(s);
      n = 0;
      ids[n++] = 6;
      for (unsigned a = 0; a < 10; a++) if ((S >> a & 1) && a != 6) ids[n++] = a;
      s = idstore(c, n, ids);
      bool disjoint89 = !(S >> 8 & 1) && !(S >> 9 & 1);
      okSix &= admits(s, "absent 9; make 8 @8") == disjoint89;
      tr_state_free(s);
    }
    for (unsigned S = 0; S < 16; S++)
      for (size_t number = 0; number <= 6; number++) {
        tr_occ ids[5];
        const char *labels[5] = {"5", "5", "5", "5", "5"};
        size_t n = 0;
        ids[n++] = 0 + 1000;
        for (unsigned a = 0; a < 4; a++) if (S >> a & 1) ids[n++] = 1000 + a + 1;
        tr_state *s = store(c, n, ids, labels);
        char text[32];
        snprintf(text, sizeof text, "count 5=%zu", number);
        okCounts &= admits(s, text) == ((size_t)__builtin_popcount(S) + 1 == number);
        tr_state_free(s);
      }
    CHECK(okFive, "unless_nine_graded / survivesFive_iff (admitted iff S disjoint from {7, 9}), 1024 surroundings");
    CHECK(okSix, "survivesSix_iff (admitted iff S disjoint from {8, 9}), 1024 surroundings");
    CHECK(okCounts, "counts_graded (admitted iff |S| + 1 = number), 16 surroundings x 7 numbers");
    tr_state *t1 = idstore(c, 2, (tr_occ[]){5, 6}), *t2 = tr_state_clone(t1);
    bool one_then = fires(t1, "absent 9; make 7 @7") && fires(t1, "absent 9; make 8 @8");
    bool other_then = fires(t2, "absent 9; make 8 @8") && fires(t2, "absent 9; make 7 @7");
    char *b1 = bag(t1), *b2 = bag(t2);
    CHECK(one_then && other_then && !strcmp(b1, b2), "they_commute (separated absence firings)");
    free(b1); free(b2);
    tr_state_free(t1); tr_state_free(t2);
  }
  tr_state_free(one);
  tr_state_free(withNine);
}

tr_member everything(tr_view *v, tr_term label, void *env) {
  (void)v; (void)label; (void)env;
  return TR_IN;
}

/* TransportControls: the watched region holds the labels 1 when the solution sets X to 1. */
static tr_term watchedX;
static tr_member watched(tr_view *v, tr_term label, void *env) {
  (void)env;
  tr_ctx *c = tr_view_ctx(v);
  if (label != tr_code(c, 1)) return TR_OUT;
  if (tr_view_same(v, watchedX, tr_code(c, 1))) return TR_IN;
  return tr_view_possible(v, watchedX, tr_code(c, 1)) ? TR_DEPENDS : TR_OUT;
}

static void lean_transport_controls(tr_ctx *c) {
  tr_state *start = tr_state_new(c);
  uint32_t x = declare(start, 1);
  watchedX = tr_var(c, x);
  tr_guard q = {.kind = TR_G_QUERY, .region = watched};
  tr_firing watcher = {.guards = &q, .nguards = 1};
  CHECK(tr_admits(start, &watcher, NULL) == TR_ADMITTED, "watcher_valid");
  tr_state *w = tr_state_clone(start);
  CHECK(fires(w, "make 1 @5"), "writer_valid");
  CHECK(tr_admits(w, &watcher, NULL) == TR_REFUSED, "watcher_refused_after_writer (at X = 1 the region holds 5)");
  tr_state *o = tr_state_clone(start);
  CHECK(fires(o, "make 0 @6") && tr_admits(o, &watcher, NULL) == TR_ADMITTED, "outsider_watcher_independent (outsider then watcher)");
  tr_state *o2 = tr_state_clone(start);
  CHECK(tr_fire(o2, &watcher, NULL) == TR_ADMITTED && fires(o2, "make 0 @6"), "outsider_watcher_independent (watcher then outsider)");
  tr_state *two = tr_state_clone(w);
  char text[64];
  snprintf(text, sizeof text, "tell $%u=2", x);
  CHECK(fires(two, text) && tr_admits(two, &watcher, NULL) == TR_ADMITTED,
        "overlap_at_one_solution_only (once X = 2 the writer is outside the region)");
  tr_state_free(start); tr_state_free(w); tr_state_free(o); tr_state_free(o2); tr_state_free(two);
}

static void lean_lawful_and_disequality_controls(tr_ctx *c) {
  /* LawfulControls: X = 1 and Y = 2 are independent; settlement by the most general unifier
   * asks nothing more than the information (settledBy_asks_more is the negative). */
  tr_state *a = tr_state_new(c);
  uint32_t x = declare(a, 2);
  tr_state *b = tr_state_clone(a);
  char one[32], two[32], askx[32];
  snprintf(one, 32, "tell $%u=1", x);
  snprintf(two, 32, "tell $%u=2", x + 1);
  snprintf(askx, 32, "ask $%u=1", x);
  tr_state *idle = tr_state_clone(a);
  CHECK(fires(idle, "") && !admits(idle, askx), "settledBy_asks_more (negative): after an idle firing X = 1 is not asked");
  CHECK(fires(a, one) && fires(a, two) && fires(b, two) && fires(b, one), "lawful_independent (tellOne, tellTwo in both orders)");
  CHECK(tr_resolve(a, tr_var(c, x)) == tr_resolve(b, tr_var(c, x)) &&
        tr_resolve(a, tr_var(c, x + 1)) == tr_resolve(b, tr_var(c, x + 1)) && admits(a, askx),
        "firstOrder_closes (both orders reach the same solutions)");
  tr_state_free(a); tr_state_free(b); tr_state_free(idle);

  /* DisequalityControls: X a variable, a and b constants, rec(a) the row recording X = a. */
  tr_state *open = tr_state_new(c);
  uint32_t X = declare(open, 1);
  char tA[32], tB[32], ap[32], abs[48];
  snprintf(tA, 32, "tell $%u=a", X);
  snprintf(tB, 32, "tell $%u=b", X);
  snprintf(ap, 32, "apart $%u=a", X);
  snprintf(abs, 48, "absent rec($%u); make marker", X);
  CHECK(admits(open, tA), "same_admitted_open");
  tr_state *after = tr_state_clone(open);
  CHECK(fires(after, ap), "tellApart_admitted");
  CHECK(tr_apart_count(after) == 1, "afterApart_disequations = [(X, a)]");
  CHECK(admits(after, tB), "other_admitted");
  CHECK(!admits(after, tA) && why(after, tA) == TR_UNSOLVABLE, "same_refused / disequality_checked");
  CHECK(admits(open, abs), "absent_record_admitted (absence of rec(X) at nothing present)");
  tr_state *openIns = tr_state_clone(open), *apartIns = tr_state_clone(after);
  CHECK(fires(openIns, "make rec(a)") && fires(apartIns, "make rec(a)"), "insert_admitted");
  CHECK(!admits(openIns, abs), "absent_record_refused (rec(X) could be rec(a))");
  CHECK(admits(openIns, tA) && !admits(apartIns, tA), "absence_vs_disequality / apart_persists_after_insert");
  CHECK(admits(apartIns, abs), "a disequation makes an absence hold that equations alone leave open (Disequality.lean)");
  CHECK(!admits(open, "apart a=a") && why(open, "apart a=a") == TR_SHAPES, "a told disequation must form a frame (Firing.formed)");
  tr_state_free(open); tr_state_free(after); tr_state_free(openIns); tr_state_free(apartIns);
}

static void lean_contextual_controls(tr_ctx *c) {
  /* ResolutionReadPortControls: goal p(X) with X the caller's variable 0; the stored clause
   * p(f(X)). with its own private variable 0. */
  tr_state *s = tr_state_new(c);
  uint32_t X = declare(s, 1);
  fb b;
  fb_init(&b, c);
  char goal[32];
  snprintf(goal, 32, "p($%u)", X);
  make_id(&b, goal, 1);
  make_schema(&b, "clause0(p(f(X)))", 1);
  b.makes[1].id = 2;
  CHECK(tr_fire(s, F(&b), NULL) == TR_ADMITTED, "before: the goal and the stored clause");
  fb_free(&b);
  tr_term schema;
  tr_present(s, 2, &schema);
  tr_state *s2 = tr_state_clone(s);
  CHECK(fires(s, "take G@1; read clause0(G)@2"), "capture_free_admitted (the read port renames apart)");
  tr_term after;
  CHECK(tr_present(s, 2, &after) && after == schema, "clause_still_stored (same unspecialized schema)");
  tr_term xv = tr_resolve(s, tr_var(c, X));
  CHECK(tr_term_kind(c, xv) == TR_APP && tr_term_kind(c, tr_term_arg(c, xv, 0)) == TR_VAR &&
        tr_term_index(c, tr_term_arg(c, xv, 0)) != X, "the goal's X = f(a fresh helper)");
  /* the one-frame reading with the clause built in and not renamed apart */
  tr_state *one = tr_state_new(c);
  uint32_t Y = declare(one, 1);
  char row[48], goal2[32];
  snprintf(goal2, 32, "make p($%u) @1", Y);
  snprintf(row, 48, "make clause0(p(f($%u))) @2", Y);
  fires(one, goal2);
  fires(one, row);
  CHECK(!admits(one, "take G@1; read clause0(G)@2") && why(one, "take G@1; read clause0(G)@2") == TR_UNSOLVABLE,
        "Resolution.Controls.capture_refused (occurs check)");
  /* two_reads_apart: two goals, the clause read at two ports in one firing */
  fb_init(&b, c);
  char g2[32];
  snprintf(g2, 32, "p($%u)", X);
  tr_state *t = tr_state_new(c);
  uint32_t Z = declare(t, 2);
  char ga[32], gb[32];
  snprintf(ga, 32, "make p($%u) @1", Z);
  snprintf(gb, 32, "make p($%u) @3", Z + 1);
  fires(t, ga);
  fires(t, gb);
  fb_free(&b);
  fb_init(&b, c);
  make_schema(&b, "clause0(p(f(X)))", 1);
  b.makes[0].id = 2;
  tr_fire(t, F(&b), NULL);
  fb_free(&b);
  CHECK(fires(t, "take G@1; take H@3; read clause0(G)@2; read clause0(H)@2"), "two reads of one clause in one firing");
  CHECK(!tr_bound(t, Z) == false && tr_resolve(t, tr_var(c, Z)) != tr_resolve(t, tr_var(c, Z + 1)),
        "two_reads_apart (the two opened copies have disjoint fresh variables)");
  tr_state_free(s); tr_state_free(s2); tr_state_free(one); tr_state_free(t);

  /* ContextualDiamond: helper firings make an occurrence and a fresh helper with a told value. */
  tr_state *h1 = tr_state_new(c), *h2;
  h2 = tr_state_clone(h1);
  const char *f1 = "make h(H); tell H=c1", *f2 = "make h(H); tell H=c2";
  CHECK(fires(h1, f1) && fires(h1, f2) && fires(h2, f2) && fires(h2, f1), "helper_closes (both orders admitted)");
  CHECK(!tr_state_equal(h1, h2), "Consumer.composites_differ (helpers in two orders)");
  char *b1 = bag(h1), *b2 = bag(h2);
  CHECK(!strcmp(b1, b2), "the composites are isomorphic (swapIso: same occurrences at every solution)");
  free(b1); free(b2);
  tr_state *h3 = tr_state_new(c);
  uint32_t W = declare(h3, 1);
  char hg[64], hb[32];
  snprintf(hg, 64, "make h(H); tell H=a; ask $%u=a", W);
  snprintf(hb, 32, "tell $%u=a", W);
  CHECK(!admits(h3, hg), "entails_information_iff (the helper's equation never constrains old names)");
  CHECK(fires(h3, hb) && admits(h3, hg), "entails_information_iff (positive: once the old name is a)");
  tr_state_free(h1); tr_state_free(h2); tr_state_free(h3);
}

/* ---- every solution, not only the most general unifier ---- */
static int at_mgu_only_count;
static tr_term at_mgu_pattern;
static int count_at_mgu(tr_view *v, void *env) { /* the wrong rule, as a host guard */
  (void)env;
  int n = 0;
  tr_term p = tr_view_resolve(v, at_mgu_pattern), l;
  for (tr_occ o = tr_view_next_present(v, 0, &l); o; o = tr_view_next_present(v, o, &l)) n += l == p;
  return n == at_mgu_only_count;
}

static void every_solution_controls(tr_ctx *c) {
  tr_state *s = store(c, 2, (tr_occ[]){1, 2}, (const char *[]){"p(a)", "p(b)"});
  uint32_t X = declare(s, 1);
  char t[96];
  snprintf(t, sizeof t, "absent p($%u)", X);
  CHECK(!admits(s, t), "absence with an open variable: p(X) could be p(a) -> refused");
  snprintf(t, sizeof t, "count p($%u)=0", X);
  CHECK(!admits(s, t), "count 0 with an open variable -> refused");
  at_mgu_only_count = 0;
  at_mgu_pattern = tr_var(c, 0);
  {
    char pat[32];
    snprintf(pat, 32, "p($%u)", X);
    tr_scope *sc = tr_scope_new();
    at_mgu_pattern = tr_read(c, sc, pat);
    tr_scope_free(sc);
    tr_guard g = {.kind = TR_G_HOST, .entailed = count_at_mgu};
    tr_firing f = {.guards = &g, .nguards = 1};
    CHECK(tr_admits(s, &f, NULL) == TR_ADMITTED, "negative control: counting only at the mgu would admit count p(X) = 0");
  }
  snprintf(t, sizeof t, "count p($%u)=1", X);
  CHECK(!admits(s, t), "count 1 with an open variable: 0 at the mgu, 1 at X = a -> refused");
  snprintf(t, sizeof t, "count p($%u)=1; tell $%u=a", X, X);
  CHECK(admits(s, t), "count 1 with X told a in the same firing -> admitted");
  snprintf(t, sizeof t, "absent p($%u); apart $%u=a; apart $%u=b", X, X, X);
  CHECK(admits(s, t), "absence holds when disequations exclude every match");
  snprintf(t, sizeof t, "absent p($%u); apart $%u=a", X, X);
  CHECK(!admits(s, t), "absence refused when one match is still possible (X = b)");
  CHECK(!admits(s, "absent p(Y)"), "a guard-local variable is shared by all occurrences: absent p(Y) refused");
  CHECK(admits(s, "absent q(Y)"), "absent q(Y) with no q present: admitted");
  CHECK(!admits(s, "count p(Y)=2"), "count p(Y) = 2 refused: no single solution makes both p(a) and p(b) match");
  CHECK(admits(s, "count p(a)=1") && admits(s, "count p(c)=0"), "ground counts");
  /* labels with open variables */
  tr_state *u = tr_state_new(c);
  uint32_t V = declare(u, 1);
  snprintf(t, sizeof t, "make p($%u) @9", V);
  fires(u, t);
  CHECK(!admits(u, "count p(a)=1") && !admits(u, "count p(a)=0"), "a label p(V) with V open: neither count of p(a) holds at every solution");
  tr_state *u1 = tr_state_clone(u), *u2 = tr_state_clone(u);
  snprintf(t, sizeof t, "tell $%u=a", V);
  fires(u1, t);
  snprintf(t, sizeof t, "tell $%u=b", V);
  fires(u2, t);
  CHECK(admits(u1, "count p(a)=1") && admits(u2, "count p(a)=0"), "once V is told, the count is determined");
  snprintf(t, sizeof t, "ask $%u=a", V);
  CHECK(!admits(u, t), "ask V = a with V open: refused");
  snprintf(t, sizeof t, "ask $%u=a; tell $%u=a", V, V);
  CHECK(admits(u, t), "ask V = a with the tell in the same firing: admitted");
  tr_state_free(s); tr_state_free(u); tr_state_free(u1); tr_state_free(u2);
}

/* A host guard: its first term is the same ground term at every solution. */
static int is_ground(tr_view *v, void *env) { return tr_view_ground(v, *(tr_term *)env); }

/* ---- every solution, by brute force ----
 * A naive model written from the statement (Frames.Entails, Disequality.entails_iff): labels
 * p(t) and q(t) with t a code 1..3 or a frame variable V0, V1; a firing tells equations and
 * disequations over V0, V1 and a local L, and guards with an absence or a count of p(u).  For
 * terms of depth one, a solution is fixed by which of the codes 1..3 or which of three values
 * fresh to everything (101..103) each variable takes, so enumerating those 6^3 assignments
 * enumerates the solutions.  The firing is admitted iff some assignment solves the information
 * and separates every disequation, and the guard holds at every such assignment. */
enum { BV0, BV1, BL, BNV };
static uint64_t brng = 88172645463325252ULL;
static unsigned brnd(unsigned n) {
  brng ^= brng << 13, brng ^= brng >> 7, brng ^= brng << 17;
  return (unsigned)(brng % n);
}
/* -3 L, -2 V1, -1 V0 (L only where a local may be), 0..2 the codes 1..3 */
static int bterm(bool local) { return local ? (int)brnd(6) - 3 : (int)brnd(5) - 2; }
static int bval(int t, const int *as) { return t < 0 ? as[-t - 1] : t + 1; }

static void brute_force_controls(tr_ctx *c) {
  int agree = 0, disagree = 0, admitted = 0, cases = 20000;
  for (int k = 0; k < cases; k++) {
    tr_state *s = tr_state_new(c);
    uint32_t V = declare(s, 2);
    int nl = (int)brnd(5), lab[4][2], neq = (int)brnd(3), eq[2][2], nap = (int)brnd(3), ap[2][2];
    for (int i = 0; i < nl; i++) lab[i][0] = (int)brnd(2), lab[i][1] = bterm(false);
    for (int i = 0; i < neq; i++) eq[i][0] = bterm(true), eq[i][1] = bterm(true);
    for (int i = 0; i < nap; i++) ap[i][0] = bterm(true), ap[i][1] = bterm(true);
    int pat = bterm(true), number = (int)brnd(4) - 1; /* -1: absence */
    char text[64], term[3][16];
    for (int i = 0; i < nl; i++) {
      int t = lab[i][1];
      snprintf(text, sizeof text, t < 0 ? "make %s($%u)" : "make %s(%d)", lab[i][0] ? "q" : "p", t < 0 ? V + (unsigned)(-t - 1) : (unsigned)t + 1);
      fires(s, text);
    }
    fb b;
    fb_init(&b, c);
    for (int v = 0; v < 2; v++) snprintf(term[v], 16, "$%u", V + (unsigned)v);
    snprintf(term[2], 16, "L");
    T(&b, "L");
#define BT(t) ((t) < 0 ? term[-(t) - 1] : (char[2]){(char)('1' + (t)), 0})
    for (int i = 0; i < neq; i++) tell(&b, BT(eq[i][0]), BT(eq[i][1]));
    for (int i = 0; i < nap; i++) apart(&b, BT(ap[i][0]), BT(ap[i][1]));
    char p[24];
    snprintf(p, sizeof p, "p(%s)", BT(pat));
    if (number < 0) absent(&b, p);
    else count(&b, p, (size_t)number);
#undef BT
    tr_verdict got = tr_admits(s, F(&b), NULL);
    fb_free(&b);
    /* the naive model */
    bool formed = true, solvable = false, holds = true;
    for (int i = 0; i < nap; i++) formed &= ap[i][0] != ap[i][1];
    int as[BNV];
    for (int x = 0; x < 216 && formed; x++) {
      as[0] = x % 6, as[1] = x / 6 % 6, as[2] = x / 36;
      for (int v = 0; v < BNV; v++) as[v] = as[v] < 3 ? as[v] + 1 : 101 + as[v] - 3;
      bool sol = true;
      for (int i = 0; i < neq; i++) sol &= bval(eq[i][0], as) == bval(eq[i][1], as);
      for (int i = 0; i < nap; i++) sol &= bval(ap[i][0], as) != bval(ap[i][1], as);
      if (!sol) continue;
      solvable = true;
      int n = 0;
      for (int i = 0; i < nl; i++) n += !lab[i][0] && bval(lab[i][1], as) == bval(pat, as);
      holds &= n == (number < 0 ? 0 : number);
    }
    bool want = formed && solvable && holds;
    if (want == (got == TR_ADMITTED)) agree++;
    else if (disagree++ < 3) {
      fprintf(stderr, "  brute force case %d: model %d, tcalc_ref verdict %d; labels", k, want, got);
      for (int i = 0; i < nl; i++) fprintf(stderr, " %c(%d)", lab[i][0] ? 'q' : 'p', lab[i][1]);
      fprintf(stderr, "; tells");
      for (int i = 0; i < neq; i++) fprintf(stderr, " %d=%d", eq[i][0], eq[i][1]);
      fprintf(stderr, "; apart");
      for (int i = 0; i < nap; i++) fprintf(stderr, " %d!=%d", ap[i][0], ap[i][1]);
      fprintf(stderr, "; guard p(%d) count %d (terms: -1 V0, -2 V1, -3 L, k code k+1)\n", pat, number);
    }
    admitted += want;
    tr_state_free(s);
  }
  CHECK(disagree == 0, "every solution, brute force over 20,000 random stores, tells, disequations and guards");
  CHECK(admitted > cases / 10 && admitted < cases * 9 / 10, "the brute-force cases admit and refuse in both directions");
}

/* KnowledgeTensorCoreGradeControls and HelperZonedControls. */
static void grade_controls(tr_ctx *c) {
  tr_state *bare = tr_state_new(c);
  uint32_t X = declare(bare, 1);
  char pins[32], made[32];
  snprintf(pins, sizeof pins, "tell $%u=5", X);
  snprintf(made, sizeof made, "make $%u @77", X);
  tr_state *a = tr_state_clone(bare), *b = tr_state_clone(bare);
  CHECK(fires(a, pins) && fires(a, "absent 9") && fires(b, "absent 9") && fires(b, pins),
        "the_two_orders_are_one_trace (nothing present)");
  tr_state *ctx = tr_state_clone(bare);
  fires(ctx, made); /* one occurrence labelled by the variable */
  tr_state *p = tr_state_clone(ctx);
  CHECK(fires(p, pins) && admits(p, "absent 9"), "tell_first_is_in_the_grade (every solution reads it as 5)");
  CHECK(!admits(ctx, "absent 9"), "ask_first_is_not_in_the_grade (some solution reads it as 9)");
  /* the helper pinned to 42; a firing makes occurrence 3 and a helper, guarded by the pin */
  tr_state *h = tr_state_new(c);
  uint32_t H = declare(h, 1);
  char pin[32], use[96];
  snprintf(pin, sizeof pin, "tell $%u=42", H);
  fires(h, pin);
  snprintf(use, sizeof use, "make 3 @3; tell G=g($%u); ask $%u=42", H, H);
  tr_state *h2 = tr_state_clone(h);
  CHECK(admits(h, use), "a_helper_run_is_a_zoned_proof (admitted where nothing is present)");
  CHECK(fires(h2, "make other @3") && why(h2, use) == TR_FITS, "no_run_where_the_occurrence_is_present");
  tr_state *list[] = {bare, a, b, ctx, p, h, h2};
  for (size_t i = 0; i < sizeof list / sizeof *list; i++) tr_state_free(list[i]);
}

static void view_controls(tr_ctx *c) {
  tr_state *s = tr_state_new(c);
  uint32_t X = declare(s, 2);
  CHECK(tr_vars(s) == X + 2 && tr_symbol_arity(c, tr_symbol(c, "pair", 2)) == 2, "frame size and symbol arity");
  tr_term t = tr_var(c, X);
  tr_guard g = {.kind = TR_G_HOST, .entailed = is_ground, .env = &t};
  tr_firing f = {.guards = &g, .nguards = 1};
  CHECK(tr_admits(s, &f, NULL) == TR_REFUSED, "ground(X) with X open: refused");
  char text[64];
  snprintf(text, sizeof text, "tell $%u=f($%u)", X, X + 1);
  tr_state *s1 = tr_state_clone(s);
  fires(s1, text);
  CHECK(tr_admits(s1, &f, NULL) == TR_REFUSED, "ground(X) with X = f(Y), Y open: refused");
  snprintf(text, sizeof text, "tell $%u=a", X + 1);
  fires(s1, text);
  CHECK(tr_admits(s1, &f, NULL) == TR_ADMITTED, "ground(X) once X = f(a): admitted");
  tr_state_free(s);
  tr_state_free(s1);
}

/* ---- the audit's semantic controls, restated ---- */
static int mod_zero(tr_view *v, void *env) { /* X mod Y = 0 for the codes X, Y */
  tr_term *xy = env;
  int64_t x, y;
  if (!tr_view_code(v, xy[0], &x) || !tr_view_code(v, xy[1], &y) || y == 0) return 0;
  return x % y == 0;
}

static void audit_controls(tr_ctx *c) {
  /* k03 guards never bypassed, on every entry point */
  tr_state *s = store(c, 2, (tr_occ[]){1, 2}, (const char *[]){"a", "b"});
  tr_state *before = tr_state_clone(s);
  CHECK(!admits(s, "take a@1; absent b; make z") && !fires(s, "take a@1; absent b; make z"), "k03 absence false: refused by admits and fire");
  CHECK(!fires(s, "take a@1; count b=2; make z") && tr_state_equal(s, before), "k03 count false: refused, state unchanged");
  {
    fb b;
    fb_init(&b, c);
    take(&b, "a", 1);
    absent(&b, "b");
    make(&b, "z");
    CHECK(tr_run(s, F(&b), 1) == 0 && tr_state_equal(s, before), "k03 through a run: refused, unchanged");
    fb_free(&b);
  }
  /* k04, k29, k30 names minted before use */
  tr_state *n = tr_state_new(c);
  CHECK(why(n, "make fa(@0)") == TR_SHAPES && !fires(n, "make fa(@0)"), "k04 a name used before it is minted is refused (fire and admits)");
  tr_result r = {0};
  CHECK(run1(n, "make t; mint 1; make tag(#0)", true, &r) == TR_ADMITTED && r.first_name == 0, "k30 a fresh firing mints the name 0");
  CHECK(fires(n, "make fa(@0)"), "k30 a minted name is then accepted");
  CHECK(fires(n, "make c(0)") && admits(n, "absent c(@0)") && admits(n, "absent fa(0)"), "k04 the name 0 is not the code 0");
  /* the scene: keep T |- A(x); take T |- U; keep U, fresh n |- B(n); keep A(x), keep B(x) |- W */
  tr_state *sc = tr_state_new(c);
  fires(sc, "make t @1");
  CHECK(!fires(sc, "read t@1; make fa(@0)"), "k29 scene: keep T |- A(x) with x not minted is refused");
  CHECK(fires(sc, "take t@1; make u @2"), "k29 scene: take T |- U");
  tr_result rn = {0};
  CHECK(run1(sc, "read u@2; mint 1; make fb(#0) @3", true, &rn) == TR_ADMITTED, "k29 scene: keep U, fresh n |- B(n)");
  CHECK(!fires(sc, "read fa(@0)@4; read fb(@0)@3; make w"), "k29 scene: W is not derived");
  CHECK(bag_is(sc, "fb(@0) u"), "k29 scene: the store holds only U and B(n)");
  /* the scene with x minted first: n is a new name, so B(n) is not B(x) */
  tr_state *sm = tr_state_new(c);
  fires(sm, "make t @1");
  fires(sm, "mint 1; make minted(#0) @9");
  CHECK(fires(sm, "read t@1; make fa(@0) @4") && fires(sm, "take t@1; make u @2"), "k29 minted scene: A(x), U");
  CHECK(run1(sm, "read u@2; mint 1; make fb(#0) @3", true, &rn) == TR_ADMITTED && rn.first_name == 1, "k29 minted scene: n = name 1");
  CHECK(!fires(sm, "read fa(X)@4; read fb(X)@3; make w"), "k29 minted scene: keep A(X), keep B(X) is refused (x and n are distinct names)");
  CHECK(fires(sm, "read fa(@0)@4; read fb(@1)@3; make w"), "k29 minted scene, positive: A(x) and B(n) are both present");
  /* k05 one take consumes exactly one copy; k33 a conversion replaces its source */
  tr_state *k = store(c, 3, (tr_occ[]){1, 2, 3}, (const char *[]){"a", "a", "b"});
  CHECK(!fires(k, "take a@1; take a@1; make z"), "k05 one occurrence taken twice: refused");
  CHECK(fires(k, "take a@1; make c") && bag_is(k, "a b c"), "k05/k33 one take consumes exactly one copy, the other stays");
  CHECK(fires(k, "take a@2; take b@3; make d") && bag_is(k, "c d"), "k05 two takes consume two occurrences");
  CHECK(!fires(k, "take a@2; make e"), "k05 a consumed occurrence cannot be taken again");
  /* k07 keep leaves the fact; a firing removes only what it takes */
  tr_state *kk = store(c, 2, (tr_occ[]){1, 2}, (const char *[]){"a", "b"});
  CHECK(fires(kk, "read a@1; make c") && bag_is(kk, "a b c"), "k07 keep leaves the fact");
  CHECK(!admits(kk, "absent a") && admits(kk, "absent z"), "k07 an absence query sees exactly the stores firings produce");
  /* k15, k22, k25 a refusal leaves no trace */
  tr_state *u = tr_state_new(c);
  uint32_t X = declare(u, 1);
  fires(u, "make q(1) @5");
  tr_state *u0 = tr_state_clone(u);
  char t[128];
  snprintf(t, sizeof t, "take q(N)@5; tell $%u=N; make got($%u); mint 2; absent q(1)", X, X);
  tr_result rr = {0};
  CHECK(run1(u, t, true, &rr) == TR_REFUSED && rr.reason == TR_GUARD, "k25 refused at its last check (after unification, with makes and mints)");
  CHECK(tr_state_equal(u, u0) && !tr_bound(u, X) && tr_names(u) == 0 && bag_is(u, "q(1)"), "k15 state, bindings and counters unchanged");
  snprintf(t, sizeof t, "take q(N)@5; tell $%u=N; make got($%u)", X, X);
  tr_state *u2 = tr_state_clone(u0);
  CHECK(fires(u, t) && fires(u2, t) && tr_state_equal(u, u2), "k22 a later firing is judged as if the refused one never ran");
  /* k20 a firing makes exactly its makes, once each */
  tr_state *m = tr_state_new(c);
  CHECK(fires(m, "make a; make a; make b") && bag_is(m, "a a b") && tr_present_count(m) == 3, "k20 three makes, three occurrences");
  /* k23 every fact is a well-formed term of the frame */
  CHECK(why(m, "make f($7)") == TR_SHAPES && why(m, "make f(L)") != TR_SHAPES && why(m, "make g(#0)") == TR_SHAPES,
        "k23 undeclared variable or undeclared fresh name: refused; a local of the firing: accepted");
  /* k26 an absence query sees every fact, wherever it was made */
  tr_state *w = tr_state_new(c);
  fires(w, "mint 1; make made_here(#0)");
  CHECK(!admits(w, "absent made_here(X)"), "k26 a fact made by an earlier fresh firing is seen");
  /* k27 a write to one occurrence changes no other occurrence */
  tr_state *sh = store(c, 2, (tr_occ[]){1, 2}, (const char *[]){"s(a)", "s(a)"});
  tr_term l1, l2;
  tr_present(sh, 2, &l1);
  fires(sh, "take s(a)@1; make t");
  CHECK(tr_present(sh, 2, &l2) && l1 == l2 && bag_is(sh, "s(a) t"), "k27 the other copy keeps its label");
  /* k35 an unbound unknown is not a value until a tell binds it */
  tr_state *ar = tr_state_new(c);
  uint32_t A = declare(ar, 1);
  tr_term xy[2] = {tr_var(c, A), tr_code(c, 3)};
  tr_guard g = {.kind = TR_G_HOST, .entailed = mod_zero, .env = xy};
  tr_firing f = {.guards = &g, .nguards = 1};
  CHECK(tr_admits(ar, &f, NULL) == TR_REFUSED, "k35 X mod 3 = 0 with X unbound: refused (X itself is a solution)");
  snprintf(t, sizeof t, "tell $%u=9", A);
  fires(ar, t);
  CHECK(tr_admits(ar, &f, NULL) == TR_ADMITTED, "k35 after X = 9 is told: admitted");
  tr_state *ar2 = tr_state_new(c);
  uint32_t A2 = declare(ar2, 1);
  snprintf(t, sizeof t, "tell $%u=10", A2);
  fires(ar2, t);
  xy[0] = tr_var(c, A2);
  CHECK(tr_admits(ar2, &f, NULL) == TR_REFUSED, "k35 negative: 10 mod 3 != 0");
  /* k13 only a firing changes the store: admits never does */
  tr_state *k13 = store(c, 1, (tr_occ[]){1}, (const char *[]){"a"});
  tr_state *k13b = tr_state_clone(k13);
  CHECK(admits(k13, "take a@1; make b") && tr_state_equal(k13, k13b), "k13 deciding admission changes nothing");
  /* k28: capture is avoided by opening stored schemas at fresh scopes (see the read-port controls) */
  tr_state *list[] = {s, before, n, sc, sm, k, kk, u, u0, u2, m, w, sh, ar, ar2, k13, k13b};
  for (size_t i = 0; i < sizeof list / sizeof *list; i++) tr_state_free(list[i]);
}

static void reader_and_terms(tr_ctx *c) {
  tr_scope *sc = tr_scope_new();
  tr_term a = tr_read(c, sc, "f(X, g(Y), 3, @2, $1, #0)");
  tr_term a2 = tr_read(c, sc, "f(X, g(Y), 3, @2, $1, #0)");
  CHECK(a == a2 && a != TR_NONE, "hash-consing: equal terms have equal ids");
  CHECK(tr_name(c, 0) != tr_code(c, 0), "NAME 0 and CODE 0 are distinct");
  CHECK(tr_read(c, sc, "f(a,") == TR_NONE, "reader refuses a syntax error");
  CHECK(tr_symbol(c, "f", 1) != tr_symbol(c, "f", 2), "f/1 and f/2 are distinct symbols");
  /* no fixed arity limit: a symbol of arity 1000 */
  tr_term *args = malloc(1000 * sizeof *args);
  for (int i = 0; i < 1000; i++) args[i] = tr_code(c, i);
  uint32_t big = tr_symbol(c, "big", 1000);
  tr_term t = tr_app(c, big, args);
  CHECK(tr_term_arity(c, t) == 1000 && tr_term_arg(c, t, 999) == tr_code(c, 999), "arity 1000");
  tr_state *s = tr_state_new(c);
  fb b;
  fb_init(&b, c);
  for (int i = 0; i < 100; i++) { char m[32]; snprintf(m, sizeof m, "item(%d)", i); make(&b, m); }
  CHECK(tr_fire(s, F(&b), NULL) == TR_ADMITTED && tr_present_count(s) == 100, "100 makes in one firing");
  fb_free(&b);
  fb_init(&b, c);
  for (int i = 0; i < 100; i++) { char m[32]; snprintf(m, sizeof m, "item(%d)", i); take(&b, m, (tr_occ)i + 1); }
  CHECK(tr_fire(s, F(&b), NULL) == TR_ADMITTED && tr_present_count(s) == 0, "100 takes in one firing");
  fb_free(&b);
  free(args);
  tr_state_free(s);
  tr_scope_free(sc);
  /* deep terms: a list of depth 1,000,000 whose spine holds locals, taken and made again */
  uint32_t cons = tr_symbol(c, "cons", 2);
  tr_term g = tr_const(c, "nil"), p = tr_local(c, 0);
  for (long i = 0; i < 1000000; i++) {
    tr_term ga[2] = {tr_code(c, i % 7), g}, pa[2] = {tr_local(c, 1 + (uint32_t)(i % 3)), p};
    g = tr_app(c, cons, ga);
    p = tr_app(c, cons, pa);
  }
  tr_state *d = tr_state_new(c);
  tr_make mk = {g, 7, 0};
  tr_firing f0 = {.makes = &mk, .nmakes = 1};
  tr_fire(d, &f0, NULL);
  tr_use u = {p, 7};
  tr_make again = {p, 8, 0};
  tr_firing f1 = {.locals = 4, .takes = &u, .ntakes = 1, .makes = &again, .nmakes = 1};
  CHECK(tr_admits(d, &f1, NULL) == TR_REFUSED, "deep: the spine's three locals cannot match seven codes");
  tr_term q = tr_local(c, 0);
  for (long i = 0; i < 1000000; i++) {
    tr_term qa[2] = {tr_local(c, 1 + (uint32_t)(i % 7)), q};
    q = tr_app(c, cons, qa);
  }
  u.pattern = q;
  again.label = q;
  f1.locals = 8;
  tr_term l;
  CHECK(tr_fire(d, &f1, NULL) == TR_ADMITTED && tr_present(d, 8, &l) && l == g, "deep: depth 1,000,000 unified and made again");
  tr_state_free(d);
}

int main(void) {
  tr_ctx *c = tr_ctx_new();
  reader_and_terms(c);
  lean_tensor_controls(c);
  lean_transport_controls(c);
  lean_lawful_and_disequality_controls(c);
  lean_contextual_controls(c);
  every_solution_controls(c);
  brute_force_controls(c);
  grade_controls(c);
  view_controls(c);
  audit_controls(c);
  tr_ctx_free(c);
  printf("test_ref: %d passed, %d failed\n", passed, failed);
  return failed != 0;
}
