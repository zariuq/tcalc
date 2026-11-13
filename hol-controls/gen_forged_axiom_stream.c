/* Generator for an adversarial HOLRPLY1 stream.
 *
 * usage: gen_forged_axiom_stream GENUINE.holr OUT.holr
 *
 * The stream copies the kernel hash from a genuine stream, selects the open
 * policy in its own header, introduces the axiom `|- p` for a boolean variable
 * p, and emits it.  A replay checker that reports success for this stream
 * without naming the policy and the user axiom lets any sequent be "replayed". */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char buf[4096];
static size_t n;

static void put(unsigned char b) { buf[n++] = b; }
static void put_bytes(const void *p, size_t len) { memcpy(buf + n, p, len); n += len; }
static void put_name(const char *s) {
  put(0x01);
  put((unsigned char)strlen(s));
  put_bytes(s, strlen(s));
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: %s GENUINE.holr OUT.holr\n", argv[0]); return 2; }
  FILE *in = fopen(argv[1], "rb");
  unsigned char head[40];
  if (!in || fread(head, 1, 40, in) != 40 || memcmp(head, "HOLRPLY1", 8) != 0) {
    fprintf(stderr, "cannot read a HOLRPLY1 header from %s\n", argv[1]);
    return 2;
  }
  fclose(in);

  put_bytes(head, 40);              /* magic and kernel hash */
  put(1); put(0); put(0); put(0);   /* version 1, profile 0, policy 0 (open), flags 0 */
  put_name("bool");                 /* name 0 */
  put_name("p");                    /* name 1 */
  put(0x03); put(0); put(0);        /* TYAPP bool []            -> type 0 */
  put(0x04); put(1); put(0);        /* VAR p : bool             -> term 0 */
  put(0x22); put(0);                /* NEW_AXIOM |- p           -> theorem 0 */
  put(0x32); put(0);                /* EMIT theorem 0 */

  uint64_t h = 0xcbf29ce484222325ULL;
  for (size_t i = 0; i < n; i++) { h ^= buf[i]; h *= 0x100000001b3ULL; }
  put(0x7f); put(6);                /* END, six records */
  for (int i = 0; i < 8; i++) put((unsigned char)(h >> (8 * i)));

  FILE *out = fopen(argv[2], "wb");
  if (!out || fwrite(buf, 1, n, out) != n) { fprintf(stderr, "cannot write %s\n", argv[2]); return 2; }
  fclose(out);
  return 0;
}
