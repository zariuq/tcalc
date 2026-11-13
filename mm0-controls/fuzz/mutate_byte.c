/* usage: mutate_byte IN OUT OFFSET XORMASK
 * Copies IN to OUT with the byte at OFFSET xor-ed with XORMASK (decimal or 0x..). */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  if (argc != 5) { fprintf(stderr, "usage: %s IN OUT OFFSET XORMASK\n", argv[0]); return 2; }
  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror(argv[1]); return 2; }
  fseek(in, 0, SEEK_END);
  long sz = ftell(in);
  fseek(in, 0, SEEK_SET);
  unsigned char *buf = malloc((size_t)sz + 1);
  if (fread(buf, 1, (size_t)sz, in) != (size_t)sz) { fprintf(stderr, "short read\n"); return 2; }
  fclose(in);
  long off = strtol(argv[3], NULL, 0);
  long mask = strtol(argv[4], NULL, 0);
  if (off < 0 || off >= sz) { fprintf(stderr, "offset out of range (size %ld)\n", sz); return 3; }
  buf[off] ^= (unsigned char)mask;
  FILE *out = fopen(argv[2], "wb");
  if (!out || fwrite(buf, 1, (size_t)sz, out) != (size_t)sz) { perror(argv[2]); return 2; }
  fclose(out);
  return 0;
}
