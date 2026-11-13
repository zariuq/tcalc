/* mutate_mmu.c: one random edit of a .mmu file, for differential testing of proof checkers.
 *
 *   usage: mutate_mmu SEED < FILE.mmu > MUTANT.mmu
 *          mutate_mmu --prefix N < FILE.mmu > PREFIX.mmu   (the first N directives, unedited)
 *
 * Edits: replace an identifier with another identifier of the file; delete a parenthesized group;
 * duplicate a group in place; swap two adjacent groups of one list.  The edit is written to stderr.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t rng;
static size_t rnd(size_t n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return n ? (size_t)(rng % n) : 0;
}
static int idc(char c) {
  return c == '_' || c == ':' || (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  rng = strtoull(argv[1], NULL, 10) * 6364136223846793005ULL + 1442695040888963407ULL;
  size_t cap = 1 << 20, n = 0;
  char *s = malloc(cap);
  for (int c; s && (c = getchar()) != EOF;) {
    if (n + 1 >= cap) s = realloc(s, cap *= 2);
    if (s) s[n++] = (char)c;
  }
  if (!s) return 2;
  if (!strcmp(argv[1], "--prefix") && argc > 2) { /* the first N top-level groups */
    long want = strtol(argv[2], NULL, 10), done = 0;
    int depth = 0;
    size_t i = 0;
    while (i < n && done < want) {
      if (s[i] == '-' && i + 1 < n && s[i + 1] == '-') {
        while (i < n && s[i] != '\n') i++;
        continue;
      }
      if (s[i] == '(') depth++;
      if (s[i] == ')' && --depth == 0) done++;
      i++;
    }
    fwrite(s, 1, i, stdout);
    fputc('\n', stdout);
    free(s);
    return 0;
  }
  /* tokens outside comments: identifiers and groups */
  size_t *ids = malloc((n + 1) * sizeof *ids), *opens = malloc((n + 1) * sizeof *opens), nid = 0, nop = 0;
  for (size_t i = 0; i < n;) {
    if (s[i] == '-' && i + 1 < n && s[i + 1] == '-') {
      while (i < n && s[i] != '\n') i++;
      continue;
    }
    if (idc(s[i])) {
      ids[nid++] = i;
      while (i < n && idc(s[i])) i++;
      continue;
    }
    if (s[i] == '(') opens[nop++] = i;
    i++;
  }
  size_t a = 0, b = 0; /* the edit replaces s[a, b) by `rep` */
  const char *rep = "";
  size_t replen = 0;
  char *buf = NULL;
  int kind = (int)rnd(4);
  if (kind == 0 && nid > 1) {
    a = ids[rnd(nid)];
    for (b = a; b < n && idc(s[b]); b++) {}
    size_t o = ids[rnd(nid)], e = o;
    while (e < n && idc(s[e])) e++;
    rep = s + o, replen = e - o;
    fprintf(stderr, "replace %.*s by %.*s at %zu\n", (int)(b - a), s + a, (int)replen, rep, a);
  } else if (nop) {
    a = opens[rnd(nop)];
    int depth = 0;
    for (b = a; b < n; b++) {
      if (s[b] == '(') depth++;
      if (s[b] == ')' && --depth == 0) break;
    }
    b = b < n ? b + 1 : n;
    if (kind == 1) fprintf(stderr, "delete the group at %zu\n", a);
    else if (kind == 2) {
      buf = malloc(2 * (b - a) + 2);
      memcpy(buf, s + a, b - a);
      buf[b - a] = ' ';
      memcpy(buf + (b - a) + 1, s + a, b - a);
      rep = buf, replen = 2 * (b - a) + 1;
      fprintf(stderr, "duplicate the group at %zu\n", a);
    } else { /* swap with the next sibling group, if any */
      size_t c = b;
      while (c < n && (s[c] == ' ' || s[c] == '\n')) c++;
      if (c < n && s[c] == '(') {
        int d = 0;
        size_t e;
        for (e = c; e < n; e++) {
          if (s[e] == '(') d++;
          if (s[e] == ')' && --d == 0) break;
        }
        e = e < n ? e + 1 : n;
        buf = malloc(e - a + 1);
        memcpy(buf, s + c, e - c);
        memcpy(buf + (e - c), s + b, c - b);
        memcpy(buf + (e - c) + (c - b), s + a, b - a);
        rep = buf, replen = e - a;
        b = e;
        fprintf(stderr, "swap the groups at %zu and %zu\n", a, c);
      } else {
        rep = s + a, replen = b - a;
        fprintf(stderr, "no edit\n");
      }
    }
  }
  fwrite(s, 1, a, stdout);
  fwrite(rep, 1, replen, stdout);
  fwrite(s + b, 1, n - b, stdout);
  free(buf);
  free(s);
  free(ids);
  free(opens);
  return 0;
}
