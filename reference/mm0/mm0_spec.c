/* mm0_spec.c: the specification (.mm0) for mm0_ref.c, read and matched, in order, against the proof
 * file's declarations.  Included by mm0_ref.c.
 *
 * This is all reader: the lexer, the statements, and the operator-precedence parser of math strings
 * (delimiters, prefix, infixl, infixr and general notations; coercions are not read, and a notation
 * must be declared before it is used).  A statement of the specification becomes the same data the
 * proof file's declaration makes (binders as locals, terms as t.NAME), so matching compares sorts,
 * binders and dependencies, and hash-consed terms.  Whether the statements are well formed is
 * decided by the firings that check the proof file's identical statements.
 */

enum { NK_NONE, NK_PREFIX, NK_INFIXL, NK_INFIXR, NK_NOTATION };
#define PREC_MAX 1000000

typedef struct {
  bool constant;
  int tok, prec, binder;
} nlit;
typedef struct {
  int term, prec, nlits;
  nlit *lits;
} notation;
static notation *NOTS;
static int nnots, capnots;

typedef struct {
  int name, sort; /* sorts by name */
  uint32_t n;
  int *asort;     /* the arguments' sorts */
} sterm;
static sterm *STERMS;
static int nsterms, capsterms;

/* Coercions: edges between sorts; the undirected graph is acyclic, so a path is unique. */
typedef struct {
  int from, to, term;
} coe;
static coe *COES;
static int ncoes, capcoes;
static int *VSORT; /* the sort of each variable of the statement being read, by position */
static size_t capvsort;

typedef enum { SP_SORT, SP_TERM, SP_DEF, SP_AXIOM, SP_THM } spkind;
typedef struct {
  spkind kind;
  int name;
  unsigned mods;
  uint32_t n, nd; /* binders; dummies of a definition */
  binder *b;      /* sorts by name */
  int sort;       /* by name */
  uint64_t retdeps;
  bool body_given;
  tr_term body, concl;
  uint32_t nh;
  tr_term *hyps;
} specitem;
static specitem *SPEC;
static size_t nspec, capspec, specnext;
static bool have_spec;

/* ---- the primary lexer ---- */

typedef struct {
  char kind; /* 'i' identifier, 'n' number, '$' math string, or the symbol itself */
  int id;    /* identifier: its name; number: its value */
  size_t at, len;
} stok;
static stok *ST;
static size_t nst, capst, sp;
static const char *ssrc;
static size_t slen;
static unsigned char delim[256]; /* 1 left, 2 right */
static char swhere[64];

static void spec_at(void) {
  snprintf(swhere, sizeof swhere, "the specification, byte %zu", sp < nst ? ST[sp].at : slen);
  where = swhere;
}

static void spec_lex(void) {
  for (size_t i = 0; i < slen;) {
    char c = ssrc[i];
    if (c == ' ' || c == '\n') {
      i++;
      continue;
    }
    if (c == '-' && i + 1 < slen && ssrc[i + 1] == '-') {
      while (i < slen && ssrc[i] != '\n') i++;
      continue;
    }
    GROW(ST, nst, capst);
    stok *t = &ST[nst++];
    *t = (stok){c, -1, i, 1};
    if (c == '$') {
      size_t j = i + 1;
      while (j < slen && ssrc[j] != '$') {
        if ((unsigned char)ssrc[j] >= 0x80 || ssrc[j] == '\r' || ssrc[j] == '\t') {
          snprintf(swhere, sizeof swhere, "the specification, byte %zu", j);
          where = swhere;
          die("character %u is not allowed in a math string", (unsigned char)ssrc[j]);
        }
        j++;
      }
      if (j >= slen) where = "the specification", die("a math string is not closed");
      *t = (stok){'$', -1, i + 1, j - i - 1};
      i = j + 1;
    } else if (strchr("*.:;()>{}=", c))
      i++;
    else if (c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
      size_t j = i;
      while (j < slen && (ssrc[j] == '_' || (ssrc[j] >= 'a' && ssrc[j] <= 'z') || (ssrc[j] >= 'A' && ssrc[j] <= 'Z') ||
                          (ssrc[j] >= '0' && ssrc[j] <= '9')))
        j++;
      if (j - i > 1 || c != '_') *t = (stok){'i', intern(ssrc + i, j - i), i, j - i};
      i = j;
    } else if (c >= '0' && c <= '9') {
      size_t j = i;
      long v = 0;
      while (j < slen && ssrc[j] >= '0' && ssrc[j] <= '9' && v < 100000000) v = 10 * v + (ssrc[j++] - '0');
      if (c == '0' && j - i > 1) where = "the specification", die("a number with a leading zero");
      *t = (stok){'n', (int)v, i, j - i};
      i = j;
    } else {
      snprintf(swhere, sizeof swhere, "the specification, byte %zu", i);
      where = swhere;
      die("character %u is not allowed", (unsigned char)c);
    }
  }
}

static bool sis(char k) { return sp < nst && ST[sp].kind == k; }
static bool skw(const char *w) { return sis('i') && !strcmp(N[ST[sp].id].s, w); }
static void sexpect(char k) {
  spec_at();
  if (!sis(k)) die("expected '%c'", k);
  sp++;
}
static int sident(void) {
  spec_at();
  if (!sis('i')) die("expected an identifier");
  return ST[sp++].id;
}
static int sprec(void) {
  spec_at();
  if (sis('n')) return ST[sp++].id;
  if (skw("max")) return sp++, PREC_MAX;
  die("expected a precedence");
  return 0;
}

/* ---- math strings ---- */

static int *MT;
static size_t nmt, capmt, mp;

static void math_token(size_t a, size_t b) {
  if (b <= a) return;
  GROW(MT, nmt, capmt);
  MT[nmt++] = intern(ssrc + a, b - a);
}
/* Split on whitespace, then after every left delimiter and before every right delimiter. */
static void math_lex(const stok *s) {
  nmt = mp = 0;
  size_t i = s->at, end = s->at + s->len;
  while (i < end) {
    while (i < end && (ssrc[i] == ' ' || ssrc[i] == '\n')) i++;
    size_t start = i;
    for (; i < end && ssrc[i] != ' ' && ssrc[i] != '\n'; i++) {
      unsigned char c = (unsigned char)ssrc[i];
      if (delim[c] & 2) math_token(start, i), start = i;
      if (delim[c] & 1) math_token(start, i + 1), start = i + 1;
    }
    math_token(start, i);
  }
}
/* A constant: one token. */
static int constant(void) {
  spec_at();
  if (!sis('$')) die("expected a constant");
  math_lex(&ST[sp++]);
  if (nmt != 1) die("a constant is one token");
  return MT[0];
}

static int mpeek(void) { return mp < nmt ? MT[mp] : -1; }
static tr_term mexpr(int p, int *sort);

static tr_term mapp(int f, tr_term *args) {
  char *sn = xrealloc(NULL, strlen(N[STERMS[f].name].s) + 3);
  memcpy(sn, "t.", 2);
  strcpy(sn + 2, N[STERMS[f].name].s);
  tr_term t = tr_app(C, tr_symbol(C, sn, STERMS[f].n), args);
  free(sn);
  return t;
}

/* e of sort `from` where sort `to` is expected: the coercions on the path inserted. */
static bool coe_path(int from, int to, int *seen, int depth, tr_term *e) {
  if (from == to) return true;
  if (depth > ncoes) return false;
  for (int i = 0; i < ncoes; i++)
    if (COES[i].from == from && !seen[i]) {
      seen[i] = 1;
      tr_term x = mapp(COES[i].term, e);
      if (coe_path(COES[i].to, to, seen, depth + 1, &x)) {
        *e = x;
        return true;
      }
    }
  return false;
}
static tr_term coerce(tr_term e, int from, int to) {
  if (from == to) return e;
  int *seen = xrealloc(NULL, ((size_t)ncoes + 1) * sizeof *seen);
  memset(seen, 0, ((size_t)ncoes + 1) * sizeof *seen);
  bool ok = coe_path(from, to, seen, 0, &e);
  free(seen);
  if (!ok) die("an expression of sort %s where %s is expected", N[from].s, N[to].s);
  return e;
}
static tr_term marg(int p, int want) {
  int s;
  tr_term e = mexpr(p, &s);
  return coerce(e, s, want);
}

static tr_term mprimary(int p, int *level, int *sort) {
  deep();
  if (mp >= nmt) die("a math string ends early");
  int t = MT[mp++];
  if (!strcmp(N[t].s, "(")) {
    tr_term e = mexpr(0, sort);
    if (mpeek() < 0 || strcmp(N[mpeek()].s, ")")) die("expected ) in a math string");
    mp++;
    *level = PREC_MAX;
    return e;
  }
  if (N[t].svar) {
    *level = PREC_MAX;
    *sort = VSORT[N[t].svar - 1];
    return L((uint32_t)N[t].svar - 1);
  }
  if (N[t].nkind == NK_PREFIX || N[t].nkind == NK_NOTATION) {
    bool pre = N[t].nkind == NK_PREFIX;
    int q = pre ? N[t].nprec : NOTS[N[t].nidx].prec, f = pre ? N[t].nterm : NOTS[N[t].nidx].term;
    if (q < p) die("%s cannot stand at precedence %d", N[t].s, p);
    const sterm *ft = &STERMS[f];
    uint32_t n = ft->n;
    tr_term *a = xrealloc(NULL, (n + 1) * sizeof *a);
    if (pre) {
      for (uint32_t k = 0; k + 1 < n; k++) a[k] = marg(PREC_MAX, ft->asort[k]);
      if (n) a[n - 1] = marg(q, ft->asort[n - 1]);
    } else {
      const notation *nt = &NOTS[N[t].nidx];
      for (int i = 1; i < nt->nlits; i++) {
        const nlit *l = &nt->lits[i];
        if (l->constant) {
          if (mpeek() != l->tok) die("expected %s in a math string", N[l->tok].s);
          mp++;
          continue;
        }
        int next = i + 1 < nt->nlits ? (nt->lits[i + 1].constant ? nt->lits[i + 1].prec + 1 : PREC_MAX) : q;
        a[l->binder] = marg(next, ft->asort[l->binder]);
      }
    }
    tr_term e = mapp(f, a);
    free(a);
    *level = q;
    *sort = ft->sort;
    return e;
  }
  if (N[t].sterm) {
    const sterm *ft = &STERMS[N[t].sterm - 1];
    uint32_t n = ft->n;
    if (n && p > 1024) die("%s cannot stand at precedence %d", N[t].s, p);
    tr_term *a = xrealloc(NULL, (n + 1) * sizeof *a);
    for (uint32_t k = 0; k < n; k++) a[k] = marg(PREC_MAX, ft->asort[k]);
    tr_term e = mapp(N[t].sterm - 1, a);
    free(a);
    *level = n ? 1024 : PREC_MAX;
    *sort = ft->sort;
    return e;
  }
  die("unknown token %s in a math string", N[t].s);
  return TR_NONE;
}

static tr_term mexpr(int p, int *sort) {
  int level;
  tr_term lhs = mprimary(p, &level, sort);
  for (int t; (t = mpeek()) >= 0;) {
    int k = N[t].nkind, q = N[t].nprec;
    if ((k != NK_INFIXL && k != NK_INFIXR) || q < p) break;
    if (level < (k == NK_INFIXL ? q : q + 1)) die("%s has a left side of too low a precedence", N[t].s);
    mp++;
    const sterm *ft = &STERMS[N[t].nterm];
    tr_term a[2] = {coerce(lhs, *sort, ft->asort[0]), marg(k == NK_INFIXL ? q + 1 : q, ft->asort[1])};
    lhs = mapp(N[t].nterm, a);
    level = q;
    *sort = ft->sort;
  }
  return lhs;
}

/* A formula; want >= 0: coerced to that sort. */
static tr_term formula(size_t tokat, int want) {
  size_t save = sp;
  sp = tokat;
  spec_at();
  sp = save;
  math_lex(&ST[tokat]);
  int s;
  tr_term e = mexpr(0, &s);
  if (mp != nmt) die("a math string has tokens left over");
  return want >= 0 ? coerce(e, s, want) : e;
}

/* ---- statements ---- */

typedef struct {
  int name; /* -1: anonymous */
  bool bound, dummy, hyp;
  int sort; /* by name */
  uint64_t deps;
  size_t fml; /* hyp: its math string */
} sbinder;

/* Binder groups { ... } and ( ... ); variables get svar = position + 1 (dummies after the rest). */
static size_t sbinders(sbinder **out, size_t *cap, bool allow_formula, bool allow_dummy) {
  size_t n = 0;
  while (sis('{') || sis('(')) {
    bool curly = sis('{');
    sp++;
    size_t first = n;
    while (!sis(':')) {
      spec_at();
      bool dummy = false;
      int nm = -1;
      if (sis('.') && allow_dummy) sp++, dummy = true;
      if (sis('_')) sp++;
      else nm = sident();
      GROW(*out, n, *cap);
      (*out)[n++] = (sbinder){nm, curly || dummy, dummy, false, -1, 0, 0};
    }
    sp++;
    if (sis('$')) {
      if (!allow_formula || curly) die("a hypothesis here");
      for (size_t i = first; i < n; i++) (*out)[i].hyp = true, (*out)[i].fml = sp;
      sp++;
    } else {
      int s = sident();
      for (size_t i = first; i < n; i++) (*out)[i].sort = s;
      uint64_t deps = 0;
      while (sis('i')) {
        int d = ST[sp++].id;
        size_t k = 0, pos = 0;
        for (; k < first; k++) {
          if ((*out)[k].name == d && (*out)[k].bound && !(*out)[k].dummy && !(*out)[k].hyp) break;
          pos += !(*out)[k].hyp && !(*out)[k].dummy;
        }
        if (k == first) die("dependency %s is not an earlier bound variable", N[d].s);
        deps |= 1ULL << pos;
      }
      for (size_t i = first; i < n; i++) (*out)[i].deps = deps;
    }
    sexpect(curly ? '}' : ')');
  }
  return n;
}

/* A type after ':' or '>': a sort and its dependencies (names of bound binders). */
static void stype(const sbinder *b, size_t nb, int *sort, uint64_t *deps) {
  *sort = sident();
  *deps = 0;
  while (sis('i')) {
    int d = ST[sp++].id;
    size_t k = 0, pos = 0;
    for (; k < nb; k++) {
      if (b[k].name == d && b[k].bound && !b[k].dummy && !b[k].hyp) break;
      pos += !b[k].hyp && !b[k].dummy;
    }
    if (k == nb) die("dependency %s is not a bound variable", N[d].s);
    *deps |= 1ULL << pos;
  }
}

static specitem *new_item(spkind kind, int name) {
  GROW(SPEC, nspec, capspec);
  specitem *it = &SPEC[nspec++];
  memset(it, 0, sizeof *it);
  it->kind = kind, it->name = name;
  return it;
}

/* The binders of an item: variables (not hypotheses), dummies last; names in scope as svar. */
static void item_binders(specitem *it, const sbinder *b, size_t nb) {
  it->b = xrealloc(NULL, (nb + 1) * sizeof *it->b);
  uint32_t n = 0;
  for (int pass = 0; pass < 2; pass++)
    for (size_t k = 0; k < nb; k++)
      if (!b[k].hyp && b[k].dummy == (pass == 1)) {
        it->b[n] = (binder){b[k].name, b[k].sort, b[k].bound, b[k].bound ? 0 : b[k].deps};
        if (b[k].name >= 0) N[b[k].name].svar = (int)n + 1;
        if (n >= capvsort) {
          capvsort = capvsort ? 2 * capvsort : 64;
          VSORT = xrealloc(VSORT, capvsort * sizeof *VSORT);
        }
        VSORT[n] = b[k].sort;
        n++;
        if (pass == 0) it->n = n;
        else it->nd++;
      }
}
static void forget_svars(const specitem *it) {
  for (uint32_t k = 0; k < it->n + it->nd; k++)
    if (it->b[k].name >= 0) N[it->b[k].name].svar = 0;
}

static void spec_statement(void) {
  spec_at();
  static sbinder *b;
  static size_t capb2;
  unsigned mods = 0;
  static const char *mod[4] = {"pure", "strict", "provable", "free"};
  for (int m = 0; m < 4; m++)
    if (skw(mod[m])) sp++, mods |= 1u << m;
  if (mods || skw("sort")) {
    spec_at();
    if (!skw("sort")) die("expected sort");
    sp++;
    specitem *it = new_item(SP_SORT, sident());
    it->mods = mods;
    sexpect(';');
    return;
  }
  if (skw("term") || skw("def")) {
    bool def = skw("def");
    sp++;
    int name = sident();
    size_t nb = sbinders(&b, &capb2, false, def);
    sexpect(':');
    int sort;
    uint64_t deps;
    for (;;) { /* term: type > type > ... > type */
      stype(b, nb, &sort, &deps);
      if (def || !sis('>')) break;
      sp++;
      GROW(b, nb, capb2);
      b[nb++] = (sbinder){-1, false, false, false, sort, deps, 0};
    }
    specitem *it = new_item(def ? SP_DEF : SP_TERM, name);
    it->sort = sort, it->retdeps = deps;
    item_binders(it, b, nb);
    GROW(STERMS, nsterms, capsterms);
    STERMS[nsterms] = (sterm){name, sort, it->n, xrealloc(NULL, (it->n + 1) * sizeof(int))};
    for (uint32_t k = 0; k < it->n; k++) STERMS[nsterms].asort[k] = it->b[k].sort;
    N[name].sterm = ++nsterms;
    if (def && sis('=')) {
      sp++;
      spec_at();
      if (!sis('$')) die("expected the definition's body");
      it->body_given = true;
      it->body = formula(sp++, sort);
    }
    forget_svars(it);
    sexpect(';');
    return;
  }
  if (skw("axiom") || skw("theorem")) {
    bool thm = skw("theorem");
    sp++;
    int name = sident();
    size_t nb = sbinders(&b, &capb2, true, false);
    sexpect(':');
    size_t *fml = NULL, nf = 0, capf = 0;
    for (;;) { /* (type | formula) > ... > formula */
      spec_at();
      if (sis('$')) {
        size_t at = sp++;
        if (!sis('>')) {
          GROW(fml, nf, capf);
          fml[nf++] = at; /* the conclusion */
          break;
        }
        GROW(b, nb, capb2);
        b[nb++] = (sbinder){-1, false, false, true, -1, 0, at};
      } else {
        int sort;
        uint64_t deps;
        stype(b, nb, &sort, &deps);
        if (!sis('>')) die("an assertion ends with a formula");
        GROW(b, nb, capb2);
        b[nb++] = (sbinder){-1, false, false, false, sort, deps, 0};
      }
      sp++;
    }
    specitem *it = new_item(thm ? SP_THM : SP_AXIOM, name);
    item_binders(it, b, nb);
    for (size_t k = 0; k < nb; k++) it->nh += b[k].hyp;
    it->hyps = xrealloc(NULL, (it->nh + 1) * sizeof *it->hyps);
    uint32_t j = 0;
    for (size_t k = 0; k < nb; k++)
      if (b[k].hyp) it->hyps[j++] = formula(b[k].fml, -1);
    it->concl = formula(fml[0], -1);
    free(fml);
    forget_svars(it);
    sexpect(';');
    return;
  }
  if (skw("delimiter")) { /* delimiter $ both $; or delimiter $ left $ $ right $; */
    sp++;
    for (int which = 0; sis('$'); which++) {
      if (which == 2) die("a delimiter statement has one or two strings");
      const stok *s = &ST[sp++];
      for (size_t i = s->at; i < s->at + s->len; i++)
        if (ssrc[i] != ' ' && ssrc[i] != '\n') {
          char c = ssrc[i];
          if (i + 1 < s->at + s->len && ssrc[i + 1] != ' ' && ssrc[i + 1] != '\n') die("a delimiter is one character");
          if (c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'))
            die("the delimiter %c consists of identifier characters", c);
          delim[(unsigned char)c] |= which == 0 ? 3 : 2;
        }
      if (which == 0 && sis('$')) /* two strings: the first is left only */
        for (int c = 0; c < 256; c++)
          if (delim[c] == 3) delim[c] = 1;
    }
    sexpect(';');
    return;
  }
  if (skw("prefix") || skw("infixl") || skw("infixr")) {
    int kind = skw("prefix") ? NK_PREFIX : skw("infixl") ? NK_INFIXL : NK_INFIXR;
    sp++;
    int f = sident();
    if (!N[f].sterm) die("notation for an unknown term %s", N[f].s);
    sexpect(':');
    int c = constant();
    if (!skw("prec")) die("expected prec");
    sp++;
    int q = sprec();
    if (N[c].nkind) die("the token %s has a notation already", N[c].s);
    if (kind != NK_PREFIX && STERMS[N[f].sterm - 1].n != 2) die("an infix notation needs two arguments");
    N[c].nkind = kind, N[c].nterm = N[f].sterm - 1, N[c].nprec = q;
    sexpect(';');
    return;
  }
  if (skw("notation")) {
    sp++;
    int f = sident();
    if (!N[f].sterm) die("notation for an unknown term %s", N[f].s);
    size_t nb = sbinders(&b, &capb2, false, false);
    sexpect(':');
    int sort;
    uint64_t deps;
    stype(b, nb, &sort, &deps);
    sexpect('=');
    GROW(NOTS, nnots, capnots);
    notation *nt = &NOTS[nnots];
    *nt = (notation){N[f].sterm - 1, 0, 0, NULL};
    int capl = 0;
    while (!sis(';')) {
      spec_at();
      GROW(nt->lits, nt->nlits, capl);
      if (sis('(')) {
        sp++;
        int c = constant();
        sexpect(':');
        nt->lits[nt->nlits++] = (nlit){true, c, sprec(), -1};
        sexpect(')');
      } else {
        int v = sident(), pos = -1;
        for (size_t k = 0; k < nb; k++)
          if (b[k].name == v) pos = (int)k;
        if (pos < 0) die("%s is not a binder of the notation", N[v].s);
        nt->lits[nt->nlits++] = (nlit){false, -1, 0, pos};
      }
    }
    sp++;
    if (!nt->nlits || !nt->lits[0].constant) die("a notation begins with a constant");
    if ((uint32_t)nb != STERMS[nt->term].n) die("a notation names every argument of its term");
    for (size_t k = 0; k < nb; k++) {
      int uses = 0;
      for (int i = 0; i < nt->nlits; i++) uses += !nt->lits[i].constant && nt->lits[i].binder == (int)k;
      if (uses != 1) die("a notation names every argument of its term once");
    }
    nt->prec = nt->lits[0].prec;
    int c = nt->lits[0].tok;
    if (N[c].nkind) die("the token %s has a notation already", N[c].s);
    N[c].nkind = NK_NOTATION, N[c].nidx = nnots++;
    return;
  }
  if (skw("coercion")) { /* coercion f: from > to */
    sp++;
    int f = sident();
    if (!N[f].sterm) die("coercion by an unknown term %s", N[f].s);
    sexpect(':');
    int from = sident();
    sexpect('>');
    int to = sident();
    const sterm *ft = &STERMS[N[f].sterm - 1];
    if (ft->n != 1 || ft->asort[0] != from || ft->sort != to || from == to) die("%s is not a coercion from %s to %s", N[f].s, N[from].s, N[to].s);
    for (int i = 0; i < ncoes; i++) /* at most one path between two sorts */
      if (COES[i].from == from && COES[i].to == to) die("a second coercion from %s to %s", N[from].s, N[to].s);
    GROW(COES, ncoes, capcoes);
    COES[ncoes++] = (coe){from, to, N[f].sterm - 1};
    sexpect(';');
    return;
  }
  if (skw("input") || skw("output")) {
    while (sp < nst && !sis(';')) sp++;
    sexpect(';');
    return;
  }
  die("unknown statement");
}

static void spec_load(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) where = path, die("cannot read the specification");
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = xrealloc(NULL, (size_t)sz + 1);
  if (sz < 0 || fread(buf, 1, (size_t)sz, f) != (size_t)sz) where = path, die("cannot read the specification");
  fclose(f);
  buf[sz] = 0;
  ssrc = buf, slen = (size_t)sz;
  spec_lex();
  for (sp = 0; sp < nst;) spec_statement();
  have_spec = true;
}

/* ---- matching, in order ---- */

static specitem *spec_next(spkind kind, int name) {
  if (specnext >= nspec) die("not in the specification");
  specitem *it = &SPEC[specnext++];
  static const char *kinds[] = {"sort", "term", "def", "axiom", "theorem"};
  if (it->kind != kind || it->name != name)
    die("the specification has the %s %s here", kinds[it->kind], N[it->name].s);
  return it;
}
/* Definition bodies agree up to a renaming of their dummies (locals n and above): the walk
 * builds an injective, sort-preserving map from the specification's dummies to the proof file's. */
static bool alpha(tr_term x, tr_term y, uint32_t n, const specitem *it, const binder *b, int *to, int *from) {
  deep();
  if (x == y && x != TR_NONE) {
    if (tr_term_kind(C, x) != TR_LOCAL || tr_term_index(C, x) < n) return true;
  }
  tr_kind kx = tr_term_kind(C, x), ky = tr_term_kind(C, y);
  if (kx == TR_LOCAL && ky == TR_LOCAL && tr_term_index(C, x) >= n && tr_term_index(C, y) >= n) {
    uint32_t i = tr_term_index(C, x), j = tr_term_index(C, y);
    if (to[i] < 0 && from[j] < 0 && it->b[i].sort == SORTS[b[j].sort].name) to[i] = (int)j, from[j] = (int)i;
    return to[i] == (int)j;
  }
  if (kx != TR_APP || ky != TR_APP || tr_term_symbol(C, x) != tr_term_symbol(C, y)) return false;
  for (uint32_t k = 0; k < tr_term_arity(C, x); k++)
    if (!alpha(tr_term_arg(C, x, k), tr_term_arg(C, y, k), n, it, b, to, from)) return false;
  return true;
}

static void same_binders(const specitem *it, const binder *b, uint32_t n, uint32_t nd) {
  (void)nd;
  if (it->n != n) die("the specification has %u binders", it->n);
  for (uint32_t k = 0; k < n; k++) {
    if (it->b[k].sort != SORTS[b[k].sort].name) die("binder %u: the specification's sort is %s", k, N[it->b[k].sort].s);
    if (it->b[k].bound != b[k].bound) die("binder %u: bound in one and not in the other", k);
    if (it->b[k].deps != b[k].deps) die("binder %u: other dependencies than the specification's", k);
  }
}
static void spec_sort(int id, unsigned mods) {
  if (!have_spec) return;
  specitem *it = spec_next(SP_SORT, id);
  if (it->mods != mods) die("other sort modifiers than the specification's");
}
static void spec_term(int id, bool def, uint32_t n, uint32_t nd, const binder *b, int sort, uint64_t retdeps, tr_term body) {
  if (!have_spec) return;
  specitem *it = spec_next(def ? SP_DEF : SP_TERM, id);
  same_binders(it, b, n, nd);
  if (it->sort != SORTS[sort].name || it->retdeps != retdeps) die("another return type than the specification's");
  if (it->body_given) {
    size_t m = (size_t)(it->n + it->nd > n + nd ? it->n + it->nd : n + nd) + 1;
    int *to = xrealloc(NULL, m * sizeof *to), *from = xrealloc(NULL, m * sizeof *from);
    for (size_t i = 0; i < m; i++) to[i] = from[i] = -1;
    bool same = alpha(it->body, body, n, it, b, to, from);
    free(to);
    free(from);
    if (!same) die("another definition than the specification's");
  }
}
static void spec_assert(int id, bool thm, uint32_t n, const binder *b, uint32_t nh, const tr_term *hyps, tr_term concl) {
  if (!have_spec) return;
  specitem *it = spec_next(thm ? SP_THM : SP_AXIOM, id);
  same_binders(it, b, n, 0);
  if (it->nh != nh) die("the specification has %u hypotheses", it->nh);
  for (uint32_t j = 0; j < nh; j++)
    if (it->hyps[j] != hyps[j]) die("hypothesis %u differs from the specification's", j);
  if (it->concl != concl) die("the conclusion differs from the specification's");
}
static void spec_end(void) {
  if (have_spec && specnext < nspec) where = "the end", die("the specification's %s is not proved", N[SPEC[specnext].name].s);
}
