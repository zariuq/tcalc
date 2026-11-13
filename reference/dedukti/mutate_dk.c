/* mutate_dk.c: single-edit mutants of a Dedukti file, by the method of dk-controls/mutate_dk.sh.
 *
 *   mutate_dk FILE.dk K     writes mutant K (K = 0, 1, ...) to standard output; exit 1 when the
 *                           file has fewer than K + 1 mutants
 *   mutate_dk FILE.dk       prints the number of mutants
 *
 * The symbols the file declares are listed in order (a line that starts, after optional
 * def/thm/injective/private, with an identifier followed by ':' or '(' declares it).  Mutant K
 * is the K-th pair (line, occurrence) in reading order: on that line, that occurrence of a
 * declared symbol is replaced by the symbol declared next (the last by the first).  Identifiers
 * are [A-Za-z_][A-Za-z0-9_']*, as in the original method.
 */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *buf;
static size_t len;
static char **syms;
static size_t nsyms;

static int idstart(int c) { return isalpha(c) || c == '_'; }
static int idchar(int c) { return isalnum(c) || c == '_' || c == '\''; }

static long sym_index(const char *s, size_t n) {
  for (size_t i = 0; i < nsyms; i++)
    if (strlen(syms[i]) == n && !memcmp(syms[i], s, n)) return (long)i;
  return -1;
}

static void collect(void) {
  static const char *kw[] = {"def", "thm", "injective", "private", NULL};
  for (size_t p = 0; p < len;) {
    size_t e = p;
    while (e < len && buf[e] != '\n') e++;
    size_t q = p;
    for (;;) { /* optional keywords */
      int hit = 0;
      for (int k = 0; kw[k]; k++) {
        size_t n = strlen(kw[k]);
        if (q + n < e && !memcmp(buf + q, kw[k], n) && buf[q + n] == ' ') {
          q += n;
          while (q < e && buf[q] == ' ') q++;
          hit = 1;
        }
      }
      if (!hit) break;
    }
    if (q < e && idstart((unsigned char)buf[q])) {
      size_t s = q;
      while (q < e && idchar((unsigned char)buf[q])) q++;
      size_t n = q - s;
      while (q < e && buf[q] == ' ') q++;
      int decl = q < e && (buf[q] == '(' || (buf[q] == ':' && (q + 1 >= e || buf[q + 1] != '=')));
      int reserved = (n == 4 && !memcmp(buf + s, "Type", 4));
      for (int k = 0; kw[k]; k++) reserved |= strlen(kw[k]) == n && !memcmp(buf + s, kw[k], n);
      if (decl && !reserved && sym_index(buf + s, n) < 0) {
        syms = realloc(syms, (nsyms + 1) * sizeof *syms);
        syms[nsyms] = malloc(n + 1);
        memcpy(syms[nsyms], buf + s, n);
        syms[nsyms++][n] = 0;
      }
    }
    p = e + 1;
  }
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s FILE.dk [K]\n", argv[0]);
    return 2;
  }
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 2;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  buf = malloc((size_t)sz + 1);
  if (sz < 0 || fread(buf, 1, (size_t)sz, f) != (size_t)sz) return 2;
  fclose(f);
  len = (size_t)sz;
  buf[len] = 0;
  collect();
  long want = argc > 2 ? atol(argv[2]) : -1, k = 0;
  if (nsyms < 2) {
    if (want < 0) printf("0\n");
    return want < 0 ? 0 : 1;
  }
  for (size_t p = 0; p < len;) { /* every occurrence of a declared symbol, in reading order */
    if (idstart((unsigned char)buf[p]) && (p == 0 || !idchar((unsigned char)buf[p - 1]))) {
      size_t s = p;
      while (p < len && idchar((unsigned char)buf[p])) p++;
      long i = sym_index(buf + s, p - s);
      if (i < 0) continue;
      if (k++ == want) {
        fwrite(buf, 1, s, stdout);
        fputs(syms[(size_t)(i + 1) % nsyms], stdout);
        fwrite(buf + p, 1, len - p, stdout);
        return 0;
      }
      continue;
    }
    p++;
  }
  if (want < 0) {
    printf("%ld\n", k);
    return 0;
  }
  return 1;
}
