/* Generator for a HOLRPLY1 stream whose one theorem is about a deeply nested term.
 *
 * usage: gen_deep_term_stream GENUINE.holr OUT.holr DEPTH
 *
 * The stream copies the header of a genuine stream (kernel hash, version, profile, policy,
 * flags), builds the term  \x. \x. ... \x. x  with DEPTH abstractions over a boolean
 * variable, and emits  |- t = t  for it by REFL.  The theorem is valid at every depth; the
 * replay has to compute the type of the term and to print it, so a checker that recurses on
 * the term must either have the stack for it or say that it has no verdict. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *buf;
static size_t n;

static void put(unsigned char b) { buf[n++] = b; }
static void put_num(uint64_t v) {
  do { unsigned char b = v & 0x7f; v >>= 7; if (v) b |= 0x80; put(b); } while (v);
}
static void put_name(const char *s) {
  put(0x01);
  put((unsigned char)strlen(s));
  memcpy(buf + n, s, strlen(s)); n += strlen(s);
}

int main(int argc, char **argv) {
  if (argc != 4) { fprintf(stderr, "usage: %s GENUINE.holr OUT.holr DEPTH\n", argv[0]); return 2; }
  uint64_t depth = strtoull(argv[3], NULL, 10);
  FILE *in = fopen(argv[1], "rb");
  unsigned char head[44];
  if (!in || fread(head, 1, 44, in) != 44 || memcmp(head, "HOLRPLY1", 8) != 0) {
    fprintf(stderr, "cannot read a HOLRPLY1 header from %s\n", argv[1]);
    return 2;
  }
  fclose(in);
  buf = malloc(256 + depth * 24);
  if (!buf) { fprintf(stderr, "out of memory\n"); return 2; }

  memcpy(buf, head, 44); n = 44;    /* magic, kernel hash, version, profile, policy, flags */
  put_name("bool");                 /* name 0 */
  put_name("x");                    /* name 1 */
  put(0x03); put(0); put(0);        /* TYAPP bool []            -> type 0 */
  put(0x04); put(1); put(0);        /* VAR x : bool             -> term 0 */
  for (uint64_t i = 0; i < depth; i++) {
    put(0x07); put_num(0); put_num(i);   /* ABS x (term i)      -> term i + 1 */
  }
  put(0x10); put_num(depth);        /* REFL (term depth)        -> theorem 0 */
  put(0x32); put(0);                /* EMIT theorem 0 */

  uint64_t h = 0xcbf29ce484222325ULL;
  for (size_t i = 0; i < n; i++) { h ^= buf[i]; h *= 0x100000001b3ULL; }
  put(0x7f); put_num(depth + 6);    /* END and the number of records before it */
  for (int i = 0; i < 8; i++) put((unsigned char)(h >> (8 * i)));

  FILE *out = fopen(argv[2], "wb");
  if (!out || fwrite(buf, 1, n, out) != n) { fprintf(stderr, "cannot write %s\n", argv[2]); return 2; }
  fclose(out);
  return 0;
}
