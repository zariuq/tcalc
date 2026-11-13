/* micromath.c: Micromath's six rules as firings of tcalc_ref, against Micromath's own
 * reference kernel on random operation sequences.
 *
 * A theorem slot i holding o(A,B) = f(x(A,B), y(A,B)) is the occurrence thm(i, o, f, x, y); an
 * empty slot reads as 0 = X(0, 0).  A symbol is a generative name once minted (X = 0 and Y = 1
 * at the start, then every opaque node and every definition) and a structural code otherwise.
 * Writing a slot takes the occurrence it held.  The rules:
 *   proj1  x = X(x, y)        proj2  y = Y(x, y)        refl  a = a(X, Y)
 *   def    a fresh name n with n = f(x, y); f, x, y must be minted names
 *   substitute1, substitute2  four premises read (or taken, when one is the destination), their
 *          side conditions told as equations, the conclusion made
 * Codes are drawn from a range minting never reaches, so a code and a name never print alike.
 *
 * usage: micromath SEED OPS
 */
#include "tcalc_ref.h"
#include "kernel.h"

#include <stdlib.h>
#include <string.h>

#define SLOTS 24
#define CODE_BASE 1000000000ULL

/* Planted faults, to show the comparison catches them: 1 drops the side condition
 * v.x = u.x; 2 refuses a premise slot that is empty instead of reading 0 = X(0, 0). */
static int fault;

static uint64_t rng;
static uint64_t rnd(uint64_t n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return rng % n;
}

typedef struct {
  tr_ctx *c;
  tr_state *s;
  uint32_t thm;
  tr_occ slot[SLOTS]; /* the occurrence holding each slot, 0 when empty (control-layer index) */
} mm;

static tr_term sym(mm *m, uint64_t n) {
  return n < tr_names(m->s) ? tr_name(m->c, (uint32_t)n) : tr_code(m->c, (int64_t)n);
}
static uint64_t unsym(mm *m, tr_term t) {
  return tr_term_kind(m->c, t) == TR_NAME ? tr_term_index(m->c, t) : (uint64_t)tr_term_code(m->c, t);
}
static tr_term thm(mm *m, uint64_t i, tr_term o, tr_term f, tr_term x, tr_term y) {
  tr_term args[5] = {tr_code(m->c, (int64_t)i), o, f, x, y};
  return tr_app(m->c, m->thm, args);
}

/* Write slot i: take what it held (if anything), make the new theorem. */
static bool write(mm *m, uint64_t i, tr_term o, tr_term f, tr_term x, tr_term y, uint32_t fresh,
                  tr_use *extra_takes, size_t nextra, const tr_use *reads, size_t nreads,
                  const tr_eq *tells, size_t ntells, uint32_t locals) {
  tr_use takes[8];
  size_t nt = 0;
  for (size_t k = 0; k < nextra; k++) takes[nt++] = extra_takes[k];
  bool dest_taken = false;
  for (size_t k = 0; k < nt; k++) dest_taken |= takes[k].occ == m->slot[i];
  if (m->slot[i] && !dest_taken) {
    tr_term any[4] = {tr_local(m->c, locals), tr_local(m->c, locals + 1), tr_local(m->c, locals + 2), tr_local(m->c, locals + 3)};
    takes[nt++] = (tr_use){thm(m, i, any[0], any[1], any[2], any[3]), m->slot[i]};
    locals += 4;
  }
  tr_make mk = {thm(m, i, o, f, x, y), 0, 0};
  tr_firing fr = {.locals = locals, .fresh = fresh, .takes = takes, .ntakes = nt, .reads = reads, .nreads = nreads,
                  .makes = &mk, .nmakes = 1, .tells = tells, .ntells = ntells};
  tr_occ made;
  tr_result r = {.made = &made};
  if (tr_fire(m->s, &fr, &r) != TR_ADMITTED) return false;
  m->slot[i] = made;
  return true;
}

static bool proj1(mm *m, uint64_t x, uint64_t y, uint64_t i) {
  return write(m, i, sym(m, x), tr_name(m->c, 0), sym(m, x), sym(m, y), 0, NULL, 0, NULL, 0, NULL, 0, 0);
}
static bool proj2(mm *m, uint64_t x, uint64_t y, uint64_t i) {
  return write(m, i, sym(m, y), tr_name(m->c, 1), sym(m, x), sym(m, y), 0, NULL, 0, NULL, 0, NULL, 0, 0);
}
static bool refl(mm *m, uint64_t a, uint64_t i) {
  return write(m, i, sym(m, a), sym(m, a), tr_name(m->c, 0), tr_name(m->c, 1), 0, NULL, 0, NULL, 0, NULL, 0, 0);
}
static uint64_t opaque(mm *m) {
  tr_firing fr = {.fresh = 1};
  tr_result r = {0};
  return tr_fire(m->s, &fr, &r) == TR_ADMITTED ? r.first_name : 0;
}
/* f, x, y are written as names: an operand not yet minted is not a term of the frame. */
static uint64_t def(mm *m, uint64_t f, uint64_t x, uint64_t y, uint64_t i) {
  if (f > UINT32_MAX || x > UINT32_MAX || y > UINT32_MAX) return 0;
  uint32_t n = tr_names(m->s);
  bool ok = write(m, i, tr_fresh(m->c, 0), tr_name(m->c, (uint32_t)f), tr_name(m->c, (uint32_t)x),
                  tr_name(m->c, (uint32_t)y), 1, NULL, 0, NULL, 0, NULL, 0, 0);
  return ok ? n : 0;
}

/* The premises: each distinct slot once, read, or taken when it is the destination; an empty
 * slot is the theorem 0 = X(0, 0).  field[p][k]: o, f, x, y of premise p. */
static bool substitute(mm *m, int which, const uint64_t prem[4], uint64_t d) {
  tr_use takes[4], reads[4];
  size_t nt = 0, nr = 0;
  uint32_t locals = 0;
  tr_term field[4][4];
  for (int p = 0; p < 4; p++) {
    int first = p;
    for (int q = 0; q < p; q++)
      if (prem[q] == prem[p]) { first = q; break; }
    if (first != p) {
      memcpy(field[p], field[first], sizeof field[p]);
      continue;
    }
    if (prem[p] >= SLOTS || !m->slot[prem[p]]) {
      if (fault == 2) return false;
      for (int k = 0; k < 4; k++) field[p][k] = tr_name(m->c, 0);
      continue;
    }
    for (int k = 0; k < 4; k++) field[p][k] = tr_local(m->c, locals + (uint32_t)k);
    locals += 4;
    tr_use u = {thm(m, prem[p], field[p][0], field[p][1], field[p][2], field[p][3]), m->slot[prem[p]]};
    if (prem[p] == d) takes[nt++] = u;
    else reads[nr++] = u;
  }
  enum { O, F, X, Y };
  const tr_term *main_ = field[0], *u = field[1], *v = field[2], *x = field[3];
  tr_eq tells[7] = {{u[F], main_[X]}, {v[F], main_[Y]}, {v[X], u[X]}, {v[Y], u[Y]}};
  if (fault == 1) tells[2] = (tr_eq){v[X], v[X]};
  if (which == 1) {
    tells[4] = (tr_eq){x[F], main_[O]}, tells[5] = (tr_eq){x[X], u[X]}, tells[6] = (tr_eq){x[Y], u[Y]};
    return write(m, d, x[O], main_[F], u[O], v[O], 0, takes, nt, reads, nr, tells, 7, locals);
  }
  tells[4] = (tr_eq){x[F], main_[F]}, tells[5] = (tr_eq){x[X], u[O]}, tells[6] = (tr_eq){x[Y], v[O]};
  return write(m, d, x[O], main_[O], u[X], u[Y], 0, takes, nt, reads, nr, tells, 7, locals);
}

/* Slot i as the reference reads it. */
static ThmBody slot_body(mm *m, uint64_t i) {
  ThmBody b = {0, 0, 0, 0};
  tr_term l;
  if (i < SLOTS && m->slot[i] && tr_present(m->s, m->slot[i], &l))
    b = (ThmBody){unsym(m, tr_term_arg(m->c, l, 1)), unsym(m, tr_term_arg(m->c, l, 2)),
                  unsym(m, tr_term_arg(m->c, l, 3)), unsym(m, tr_term_arg(m->c, l, 4))};
  return b;
}

static uint64_t pick_symbol(void) {
  Symbol last = get_last_const();
  if (rnd(8) == 0) return CODE_BASE + rnd(4); /* a structural code */
  return rnd(last + 1);                       /* a minted name */
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s SEED OPS\n", argv[0]);
    return 2;
  }
  uint64_t seed = strtoull(argv[1], NULL, 10);
  long ops = strtol(argv[2], NULL, 10);
  fault = argc > 3 ? atoi(argv[3]) : 0;
  rng = seed * 6364136223846793005ULL + 1442695040888963407ULL;
  if (!init()) return 2;
  mm m = {tr_ctx_new(), NULL, 0, {0}};
  m.s = tr_state_new(m.c);
  m.thm = tr_symbol(m.c, "thm", 5);
  tr_firing start = {.fresh = 2}; /* X and Y */
  tr_fire(m.s, &start, NULL);
  long disagree = 0, accepted = 0, refused = 0, kind_accepted[7] = {0};
  for (long k = 0; k < ops; k++) {
    int op = (int)rnd(8);
    uint64_t i = rnd(SLOTS), a = pick_symbol(), b = pick_symbol(), f = pick_symbol();
    uint64_t prem[4] = {rnd(SLOTS), rnd(SLOTS), rnd(SLOTS), rnd(SLOTS)};
    if (rnd(3) == 0) prem[rnd(4)] = i; /* a premise that is also the destination */
    if (op >= 5 && rnd(2)) {
      /* prepare premises that meet the side conditions: u = main.x, v = main.y and, for
       * substitute1, x = main.out, each written by refl (so a = X, b = Y); for substitute2 the
       * main theorem is its own fourth premise.  Each write is an operation compared too. */
      ThmBody main_ = slot_body(&m, prem[0]);
      uint64_t want_of[3] = {main_.x, main_.y, main_.out};
      for (int p = 1; p <= (op == 5 ? 3 : 2); p++) {
        if (prem[p] == prem[0]) continue;
        bool w = rule_refl(want_of[p - 1], prem[p]), g = refl(&m, want_of[p - 1], prem[p]);
        if (w != g && disagree++ < 5) fprintf(stderr, "op %ld (premise refl): reference %d, tcalc_ref %d\n", k, w, g);
      }
      if (op != 5) prem[3] = prem[0];
      if (rnd(4) == 0) prem[1 + rnd(3)] = rnd(SLOTS); /* a near miss */
    }
    uint64_t want = 0, got = 0;
    switch (op) {
    case 0: want = rule_proj1(a, b, i); got = proj1(&m, a, b, i); break;
    case 1: want = rule_proj2(a, b, i); got = proj2(&m, a, b, i); break;
    case 2: want = rule_refl(a, i); got = refl(&m, a, i); break;
    case 3: if (rnd(16) == 0) { want = new_node_opaque(); got = opaque(&m); } break;
    case 4:
      if (rnd(4) == 0) {
        if (rnd(4) == 0) f = get_last_const() + 1; /* an operand not yet minted: refused by both */
        want = new_node_def(f, a, b, i);
        got = def(&m, f, a, b, i);
      }
      break;
    case 5: want = rule_substitute1(prem[0], prem[1], prem[2], prem[3], i); got = substitute(&m, 1, prem, i); break;
    default: want = rule_substitute2(prem[0], prem[1], prem[2], prem[3], i); got = substitute(&m, 2, prem, i); break;
    }
    if (want != got) {
      if (disagree++ < 5) fprintf(stderr, "op %ld (kind %d): reference %llu, tcalc_ref %llu\n", k, op,
                                   (unsigned long long)want, (unsigned long long)got);
    }
    if (got) accepted++, kind_accepted[op > 6 ? 6 : op]++;
    else refused++;
    if (k % 1000 == 999 || k == ops - 1)
      for (uint64_t j = 0; j < SLOTS; j++) {
        ThmBody x = slot_body(&m, j);
        const ThmBody *y = get_thm(j);
        if (x.out != y->out || x.f != y->f || x.x != y->x || x.y != y->y) {
          if (disagree++ < 5) fprintf(stderr, "after op %ld slot %llu differs\n", k, (unsigned long long)j);
        }
      }
  }
  printf("micromath seed %llu fault %d: %ld operations, %ld disagreements; accepted %ld (proj %ld, refl %ld, "
         "opaque %ld, def %ld, substitute1 %ld, substitute2 %ld), refused %ld; names %u, terms %zu\n",
         (unsigned long long)seed, fault, ops, disagree, accepted, kind_accepted[0] + kind_accepted[1], kind_accepted[2],
         kind_accepted[3], kind_accepted[4], kind_accepted[5], kind_accepted[6], refused, tr_names(m.s), tr_ctx_terms(m.c));
  tr_state_free(m.s);
  tr_ctx_free(m.c);
  return disagree != 0;
}
