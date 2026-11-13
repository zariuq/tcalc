/* tcs2lean.c: a rule file as Lean data, for the verified specializer.
 *
 *   usage: tcs2lean [--fault N] SRC.tcs OUT.lean GEN.c
 *
 * Reads SRC.tcs with tcs_read, the reader the generic route uses, and writes OUT.lean: every
 * theory's rules as values of SpecializedAdmission.Rule, a table of the symbols they use (the
 * reader's symbol numbers, names and arities), and a command that, when Lean checks the file,
 * writes GEN.c with SpecializedAdmission.Printer.printFile (N > 0 plants that printer fault).
 * Nothing is decided here: the file only transcribes the rules the reader built.
 */
#include "tcs.h"

#include <stdlib.h>
#include <string.h>

static uint32_t *seen;
static size_t nseen, capseen;

static void note_symbol(uint32_t s) {
  for (size_t i = 0; i < nseen; i++)
    if (seen[i] == s) return;
  if (nseen == capseen) {
    capseen = capseen ? 2 * capseen : 64;
    seen = realloc(seen, capseen * sizeof *seen);
    if (!seen) abort();
  }
  seen[nseen++] = s;
}

static void lean_string(FILE *out, const char *s) {
  fputc('"', out);
  for (; *s; s++) {
    if (*s == '"' || *s == '\\') fputc('\\', out);
    fputc(*s, out);
  }
  fputc('"', out);
}

static void term(FILE *out, const tr_ctx *c, tr_term t) {
  switch (tr_term_kind(c, t)) {
  case TR_APP: {
    uint32_t s = tr_term_symbol(c, t), n = tr_term_arity(c, t);
    note_symbol(s);
    fprintf(out, "(.app %u [", s);
    for (uint32_t i = 0; i < n; i++) {
      if (i) fputs(", ", out);
      term(out, c, tr_term_arg(c, t, i));
    }
    fputs("])", out);
    return;
  }
  case TR_CODE: fprintf(out, "(.code (%lld))", (long long)tr_term_code(c, t)); return;
  case TR_NAME: fprintf(out, "(.name %u)", tr_term_index(c, t)); return;
  case TR_VAR: fprintf(out, "(.var %u)", tr_term_index(c, t)); return;
  case TR_LOCAL: fprintf(out, "(.loc %u)", tr_term_index(c, t)); return;
  case TR_FRESH: fprintf(out, "(.fresh %u)", tr_term_index(c, t)); return;
  }
}

static void terms(FILE *out, const tr_ctx *c, const tr_term *ts, size_t n) {
  fputc('[', out);
  for (size_t i = 0; i < n; i++) {
    if (i) fputs(", ", out);
    term(out, c, ts[i]);
  }
  fputc(']', out);
}

static void eqs(FILE *out, const tr_ctx *c, const tr_eq *es, size_t n) {
  fputc('[', out);
  for (size_t i = 0; i < n; i++) {
    fputs(i ? ", (" : "(", out);
    term(out, c, es[i].left);
    fputs(", ", out);
    term(out, c, es[i].right);
    fputc(')', out);
  }
  fputc(']', out);
}

static void guard(FILE *out, const tr_ctx *c, const tcs_guard *g) {
  switch (g->kind) {
  case TCS_ASK:
    fputs("(.ask ", out), term(out, c, g->a), fputc(' ', out), term(out, c, g->b), fputc(')', out);
    return;
  case TCS_ABSENT: fputs("(.absent ", out), term(out, c, g->a), fputc(')', out); return;
  case TCS_COUNT: fputs("(.count ", out), term(out, c, g->a), fprintf(out, " %zu)", g->number); return;
  case TCS_HOST: {
    uint32_t n = tr_term_arity(c, g->a);
    fputs("(.host ", out);
    lean_string(out, tr_symbol_name(c, tr_term_symbol(c, g->a)));
    fputs(" [", out);
    for (uint32_t i = 0; i < n; i++) {
      if (i) fputs(", ", out);
      term(out, c, tr_term_arg(c, g->a, i));
    }
    fputs("])", out);
    return;
  }
  }
}

static char *slurp(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  size_t n = 0, cap = 65536;
  char *s = malloc(cap);
  if (!s) abort();
  for (size_t k; (k = fread(s + n, 1, cap - n - 1, f)) > 0;) {
    n += k;
    if (cap - n < 2) {
      cap *= 2;
      s = realloc(s, cap);
      if (!s) abort();
    }
  }
  fclose(f);
  s[n] = 0;
  return s;
}

int main(int argc, char **argv) {
  int a = 1, fault = 0;
  if (a + 1 < argc && !strcmp(argv[a], "--fault")) fault = atoi(argv[a + 1]), a += 2;
  if (argc - a != 3) {
    fprintf(stderr, "usage: %s [--fault N] SRC.tcs OUT.lean GEN.c\n", argv[0]);
    return 2;
  }
  const char *src = argv[a], *outp = argv[a + 1], *gen = argv[a + 2];
  char *text = slurp(src);
  if (!text) {
    perror(src);
    return 2;
  }
  tr_ctx *c = tr_ctx_new();
  tcs_theory *th;
  char err[256];
  int n = tcs_read(c, text, &th, err, sizeof err);
  if (n < 0) {
    fprintf(stderr, "%s: %s\n", src, err);
    return 2;
  }
  FILE *out = fopen(outp, "w");
  if (!out) {
    perror(outp);
    return 2;
  }
  fputs("import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Printer\n"
        "open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission\n\n",
        out);
  for (int ti = 0; ti < n; ti++) {
    fprintf(out, "def theory%d : String × List (String × Rule) := (", ti);
    lean_string(out, th[ti].name);
    fputs(", [", out);
    for (size_t ri = 0; ri < th[ti].nrules; ri++) {
      const tcs_rule *r = &th[ti].rules[ri];
      fputs(ri ? ",\n  (" : "\n  (", out);
      lean_string(out, r->name);
      /* Rule: nparams, fresh, takes, reads, makes, tells, aparts, guards */
      fprintf(out, ", (⟨%u, %u,\n    ", r->nparams, r->fresh);
      terms(out, c, r->takes, r->ntakes);
      fputs(",\n    ", out);
      terms(out, c, r->reads, r->nreads);
      fputs(",\n    ", out);
      terms(out, c, r->makes, r->nmakes);
      fputs(",\n    ", out);
      eqs(out, c, r->tells, r->ntells);
      fputs(",\n    ", out);
      eqs(out, c, r->apart, r->napart);
      fputs(",\n    [", out);
      for (size_t gi = 0; gi < r->nguards; gi++) {
        if (gi) fputs(", ", out);
        guard(out, c, &r->guards[gi]);
      }
      fputs("]⟩ : Rule))", out);
    }
    fputs("])\n\n", out);
  }
  fputs("def syms : List (Nat × String × Nat) := [", out);
  for (size_t i = 0; i < nseen; i++) {
    fprintf(out, "%s(%u, ", i ? ", " : "", seen[i]);
    lean_string(out, tr_symbol_name(c, seen[i]));
    fprintf(out, ", %u)", tr_symbol_arity(c, seen[i]));
  }
  fputs("]\n\ndef theories : List (String × List (String × Rule)) := [", out);
  for (int ti = 0; ti < n; ti++) fprintf(out, "%stheory%d", ti ? ", " : "", ti);
  fputs("]\n\n#eval do\n  let text ← IO.FS.readFile ", out);
  lean_string(out, src);
  fprintf(out, "\n  IO.FS.writeFile ");
  lean_string(out, gen);
  fprintf(out, " (Printer.printFile %d ", fault);
  const char *base = strrchr(src, '/');
  lean_string(out, base ? base + 1 : src);
  fputs(" text syms theories)\n  let (k, m) := Printer.specializedCount theories\n"
        "  IO.println s!\"verified specializer: {k} of {m} rules specialized\"\n",
        out);
  fclose(out);
  tcs_free(th, n);
  tr_ctx_free(c);
  free(text);
  free(seen);
  return 0;
}
